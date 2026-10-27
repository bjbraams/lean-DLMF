/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.BoundaryAsymptotics
public import DLMF.Legendre.Singularities
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import DLMF.Legendre.IntegerTheory
public import DLMF.Legendre.IntegralTools

/-!
# Definite integrals, orthogonality and primitive formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- ferrers barnes integral. -/
@[dlmf 14.17.E5]
theorem ferrers_barnes_integral {σ μ : ℂ} (hσ : -1 < σ.re) (hμ : -1 < μ.re) (ν : ℂ) :
    (∫ x : ℝ in 0..1, (x:ℂ)^σ*(1-x^2:ℂ)^(μ/2)*ferrersP ν (-μ) x)=Gamma ((σ+1)/2)*Gamma (σ/2+1)/(2^(μ+1)*Gamma ((σ-ν+μ)/2+1)*Gamma ((σ+ν+μ+3)/2)) := by
  sorry

/-- ferrers orthogonality 6. -/
@[dlmf 14.17.E6]
theorem ferrers_orthogonality_6 (l m n : ℕ) (hl : m ≤ l) (hn : m ≤ n) :
    ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (m) x=if l=n then ((n+m).factorial:ℂ)/((n-m).factorial*(n+1/2:ℂ)) else 0 := by
  have hI : (∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (m) x) = legInt_I m l n := by
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [one_mul, legInt_ferrersP_mul l n m ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩]
  rw [hI, legInt_I_eq]
  split_ifs with h
  · have hp := legInt_prod_factorial hn
    have hf : ((n-m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (2*(n:ℂ)+1) ≠ 0 := by
      have : (0:ℝ) < 2*n+1 := by positivity
      exact_mod_cast this.ne'
    rw [← hp]
    field_simp
  · simp

/-- ferrers orthogonality 7. -/
@[dlmf 14.17.E7]
theorem ferrers_orthogonality_7 (l m n : ℕ) (hl : m ≤ l) (hn : m ≤ n) :
    ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (-m) x=if l=n then (-1)^m/(l+1/2:ℂ) else 0 := by
  have hk : ((n:ℂ)-m+1) = ((n-m:ℕ):ℂ)+1 := by rw [Nat.cast_sub hn]
  have hreg : ∀ k : ℕ, (n:ℂ)-m+1 ≠ -k := fun k h => by
    rw [hk] at h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hI : (∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (-m) x) =
      (-1)^m*Gamma ((n:ℂ)-m+1)/Gamma ((n:ℂ)+m+1) *
        ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n m x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [ferrersP_negative_integer_order (n:ℂ) m hreg ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩]
    ring
  rw [hI, ferrers_orthogonality_6 l m n hl hn, hk, show (n:ℂ)+m+1 = ((n+m:ℕ):ℂ)+1 by push_cast; ring,
    Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
  split_ifs with h
  · subst h
    have hf : ((l-m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf' : ((l+m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : ((l:ℂ)+1/2) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(l.cast_nonneg : (0:ℝ) ≤ l)]
    field_simp
  · simp

/-- Nonzero polynomial degrees and integrability are explicit; singular-weight integrals retain their integrability conditions. -/
@[dlmf 14.17.E8]
theorem ferrers_orthogonality_8 (l m n : ℕ) (hl : l ≤ n) (hm : m ≤ n) (hp : 0 < m) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (m) x=if l=m then ((n+m).factorial:ℂ)/((n-m).factorial*m) else 0 := by
  split_ifs with h
  · subst h
    obtain ⟨k, rfl⟩ : ∃ k, l = k+1 := ⟨l-1, by omega⟩
    have hJ := legInt_J_eq hm
    have hd := legInt_ferrers_diag n k
    push_cast at hd ⊢
    rw [hd]
    have hf : ((n-(k+1)).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : ((k:ℂ)+1) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    rw [← hJ]; field_simp
  · exact legInt_ferrers_offdiag n l m h (by omega)

/-- Nonzero polynomial degrees and integrability are explicit; singular-weight integrals retain their integrability conditions. -/
@[dlmf 14.17.E9]
theorem ferrers_orthogonality_9 (l m n : ℕ) (hl : l ≤ n) (hm : m ≤ n) (hp : 0 < l) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (-m) x=if l=m then (-1)^l/(l:ℂ) else 0 := by
  have hk : ((n:ℂ)-m+1) = ((n-m:ℕ):ℂ)+1 := by rw [Nat.cast_sub hm]
  have hreg : ∀ k : ℕ, (n:ℂ)-m+1 ≠ -k := fun k h => by
    rw [hk] at h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hI : (∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (-m) x) =
      (-1)^m*Gamma ((n:ℂ)-m+1)/Gamma ((n:ℂ)+m+1) *
        ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n l x*ferrersP n m x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [ferrersP_negative_integer_order (n:ℂ) m hreg ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩]
    ring
  rw [hI]
  split_ifs with h
  · subst h
    rw [ferrers_orthogonality_8 l l n hl hm hp]
    simp only [↓reduceIte]
    rw [hk, show (n:ℂ)+l+1 = ((n+l:ℕ):ℂ)+1 by push_cast; ring,
      Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
    have hf : ((n-l).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf' : ((n+l).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hl0 : (l:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  · rw [legInt_ferrers_offdiag n l m h (by omega), mul_zero]

/-! ### Green's identity for order-zero Ferrers functions of general degree

The products `𝖯_ν 𝖯_λ` are integrated through Green's identity
`((1-x²)(f g' - g f'))' = (ν(ν+1) - λ(λ+1)) f g`, with the boundary form rewritten by the
recurrence 14.10.4 and evaluated at `-1` from the logarithmic behaviour of `𝖯_α` there
(DLMF 15.8.10 at `m = 0`, `legBd_zeroBalanced_isBigO`). Helper names carry the prefix `legPI`. -/
/-- `𝖯_α(x) = 𝐅(α+1,-α;1;(1-x)/2)`. -/
theorem legPI_ferrersP_zero (α : ℂ) (x : ℝ) :
    ferrersP α 0 x = regularizedGaussHG (α+1) (-α) 1 ((1-(x:ℂ))/2) := by
  simp [ferrersP]

/-- `𝖯_α` is continuous on `(-1,∞)`. -/
theorem legPI_continuousAt_ferrersP (α : ℂ) {x : ℝ} (hx : -1 < x) :
    ContinuousAt (ferrersP α 0) x := by
  have hw := legInt_half_mem_cutPlane hx
  have : ferrersP α 0 = fun y : ℝ => regularizedGaussHG (α+1) (-α) 1 ((1-(y:ℂ))/2) :=
    funext (legPI_ferrersP_zero α)
  rw [this]
  exact ContinuousAt.comp (g := regularizedGaussHG (α+1) (-α) 1)
    (differentiableAt_regularizedGaussHG _ _ _ hw).continuousAt (by fun_prop)

theorem legPI_ferrersP_one (α : ℂ) : ferrersP α 0 1 = 1 := by
  rw [legPI_ferrersP_zero]
  have h1 : ∀ k : ℕ, (1:ℂ) ≠ -(k:ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  simpa using regularizedGaussHG_zero_of_regular (a := α+1) (b := -α) h1

theorem legPI_tendsto_ferrersP_one (α : ℂ) :
    Tendsto (ferrersP α 0) (𝓝[<] (1:ℝ)) (𝓝 1) := by
  have := (legPI_continuousAt_ferrersP α (show (-1:ℝ) < 1 by norm_num)).tendsto
  rw [legPI_ferrersP_one] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem legPI_tendsto_half :
    Tendsto (fun x : ℝ => (1+x)/2) (𝓝[>] (-1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => (1+x)/2) (𝓝 (-1)) (𝓝 ((1+(-1))/2)) :=
      (tendsto_const_nhds.add tendsto_id).div_const 2
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (-1)))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : -1 < x)
    simp only [mem_Ioi]; linarith

/-- Behaviour of `𝖯_α` at `-1`: `𝖯_α(x) = -K ln((1+x)/2) + C + O(t ln t)`, `t = (1+x)/2`,
with `K = 1/(Γ(α+1)Γ(-α))`, for every `α`. -/
theorem legPI_ferrersP_neg_one_isBigO (α : ℂ) :
    (fun x : ℝ => ferrersP α 0 x + legBdK (α+1) (-α) * Real.log ((1+x)/2) -
      (legBdK' (α+1) (-α) - 2 * Real.eulerMascheroniConstant * legBdK (α+1) (-α))) =O[𝓝[>] (-1:ℝ)]
      (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) := by
  have h := (legBd_zeroBalanced_isBigO (α+1) (-α)).comp_tendsto legPI_tendsto_half
  refine h.congr_left fun x => ?_
  simp only [Function.comp_apply]
  rw [legPI_ferrersP_zero, show α + 1 + -α = 1 by ring]
  congr 3
  push_cast; ring


/-- The weight `(1-x²)^{-1/4}` used to dominate Ferrers functions on `(-1,1)`. -/
def legPIw (x : ℝ) : ℝ := ((1-x^2)/4)^(-(1/4:ℝ))

theorem legPIw_one_le {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 1 ≤ legPIw x :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by nlinarith [hx.1, hx.2]) (by nlinarith)
    (by norm_num)

theorem legPIw_pos {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 0 < legPIw x :=
  lt_of_lt_of_le one_pos (legPIw_one_le hx)

theorem legPIw_eq {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    legPIw x = ((1+x)/2)^(-(1/4:ℝ)) * ((1-x)/2)^(-(1/4:ℝ)) := by
  rw [legPIw, ← Real.mul_rpow (by linarith [hx.1]) (by linarith [hx.2])]
  congr 1; ring

/-- `|ln y| ≤ 4 y^{-1/4}` on `(0,1]`. -/
theorem legPI_abs_log_le {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    |Real.log y| ≤ 4 * y^(-(1/4:ℝ)) := by
  have h := Real.abs_log_mul_self_rpow_lt y (1/4) hy0 hy1 (by norm_num)
  have hp : 0 < y^(1/4:ℝ) := Real.rpow_pos_of_pos hy0 _
  rw [abs_mul, abs_of_pos hp, show (1:ℝ)/(1/4) = 4 by norm_num] at h
  rw [Real.rpow_neg hy0.le, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact h.le

theorem legPI_rpow_ge_one {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) : 1 ≤ y^(-(1/4:ℝ)) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by norm_num)

/-- `ln((1+x)/2) = O((1-x²)^{-1/4})` as `x → -1⁺`. -/
theorem legPI_log_isBigO_left :
    (fun x : ℝ => Real.log ((1+x)/2)) =O[𝓝[>] (-1:ℝ)] legPIw := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have ht0 : 0 < (1+x)/2 := by linarith [hx.1]
  have ht1 : (1+x)/2 ≤ 1 := by linarith [hx.2]
  have hs0 : 0 < (1-x)/2 := by linarith [hx.2]
  have hs1 : (1-x)/2 ≤ 1 := by linarith [hx.1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (legPIw_pos hx), legPIw_eq hx]
  calc |Real.log ((1+x)/2)| ≤ 4 * ((1+x)/2)^(-(1/4:ℝ)) := legPI_abs_log_le ht0 ht1
    _ ≤ 4 * (((1+x)/2)^(-(1/4:ℝ)) * ((1-x)/2)^(-(1/4:ℝ))) := by
      gcongr
      exact le_mul_of_one_le_right (Real.rpow_nonneg ht0.le _) (legPI_rpow_ge_one hs0 hs1)

/-- `ln((1-x)/2) = O((1-x²)^{-1/4})` as `x → 1⁻`. -/
theorem legPI_log_isBigO_right :
    (fun x : ℝ => Real.log ((1-x)/2)) =O[𝓝[<] (1:ℝ)] legPIw := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have ht0 : 0 < (1+x)/2 := by linarith [hx.1]
  have ht1 : (1+x)/2 ≤ 1 := by linarith [hx.2]
  have hs0 : 0 < (1-x)/2 := by linarith [hx.2]
  have hs1 : (1-x)/2 ≤ 1 := by linarith [hx.1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (legPIw_pos hx), legPIw_eq hx]
  calc |Real.log ((1-x)/2)| ≤ 4 * ((1-x)/2)^(-(1/4:ℝ)) := legPI_abs_log_le hs0 hs1
    _ ≤ 4 * (((1+x)/2)^(-(1/4:ℝ)) * ((1-x)/2)^(-(1/4:ℝ))) := by
      gcongr
      exact le_mul_of_one_le_left (Real.rpow_nonneg hs0.le _) (legPI_rpow_ge_one ht0 ht1)

theorem legPI_one_isBigO_left : (fun _ : ℝ => (1:ℝ)) =O[𝓝[>] (-1:ℝ)] legPIw := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (legPIw_pos hx), abs_one, one_mul]
  exact legPIw_one_le hx

theorem legPI_one_isBigO_right : (fun _ : ℝ => (1:ℝ)) =O[𝓝[<] (1:ℝ)] legPIw := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (legPIw_pos hx), abs_one, one_mul]
  exact legPIw_one_le hx

/-- A function continuous on `(-1,1)` and `O((1-x²)^{-1/4})` at both ends is globally bounded by a
multiple of `(1-x²)^{-1/4}`. -/
theorem legPI_bound {f : ℝ → ℂ} (hc : ContinuousOn f (Ioo (-1) 1))
    (h1 : f =O[𝓝[>] (-1:ℝ)] legPIw) (h2 : f =O[𝓝[<] (1:ℝ)] legPIw) :
    ∃ M, ∀ x ∈ Ioo (-1:ℝ) 1, ‖f x‖ ≤ M * legPIw x := by
  obtain ⟨c1, -, hc1⟩ := h1.exists_pos
  obtain ⟨c2, -, hc2⟩ := h2.exists_pos
  obtain ⟨u, hu, hU⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hc1.bound
  obtain ⟨v, hv, hV⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hc2.bound
  have hK : Icc (min u 0) (max v 0) ⊆ Ioo (-1:ℝ) 1 := by
    intro x hx
    simp only [mem_Ioi, mem_Iio] at hu hv
    constructor
    · exact lt_of_lt_of_le (lt_min hu (by norm_num)) hx.1
    · exact lt_of_le_of_lt hx.2 (max_lt hv (by norm_num))
  obtain ⟨B, hB⟩ := (isCompact_Icc).exists_bound_of_continuousOn (hc.mono hK)
  refine ⟨max (max c1 c2) (max B 0), fun x hx => ?_⟩
  have hw1 := legPIw_one_le hx
  have hw0 := legPIw_pos hx
  by_cases hxu : x < u
  · have := hU ⟨hx.1, hxu⟩
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos hw0] at this
    calc ‖f x‖ ≤ c1 * legPIw x := this
      _ ≤ _ := by gcongr; exact le_trans (le_max_left _ _) (le_max_left _ _)
  by_cases hxv : v < x
  · have := hV ⟨hxv, hx.2⟩
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos hw0] at this
    calc ‖f x‖ ≤ c2 * legPIw x := this
      _ ≤ _ := by gcongr; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hxK : x ∈ Icc (min u 0) (max v 0) :=
    ⟨le_trans (min_le_left _ _) (not_lt.mp hxu), le_trans (not_lt.mp hxv) (le_max_left _ _)⟩
  calc ‖f x‖ ≤ B := hB x hxK
    _ ≤ max B 0 := le_max_left _ _
    _ ≤ max B 0 * legPIw x := le_mul_of_one_le_right (le_max_right _ _) hw1
    _ ≤ max (max c1 c2) (max B 0) * legPIw x :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hw0.le

/-- The product of two functions dominated by `(1-x²)^{-1/4}` is integrable on `[-1,1]`. -/
theorem legPI_intervalIntegrable_mul {f g : ℝ → ℂ} (hf : ContinuousOn f (Ioo (-1) 1))
    (hg : ContinuousOn g (Ioo (-1) 1)) {M N : ℝ} (hfM : ∀ x ∈ Ioo (-1:ℝ) 1, ‖f x‖ ≤ M * legPIw x)
    (hgN : ∀ x ∈ Ioo (-1:ℝ) 1, ‖g x‖ ≤ N * legPIw x) :
    IntervalIntegrable (fun x => f x * g x) volume (-1) 1 := by
  have hI := (legInt_intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul (M*N/4^(-1/2:ℝ))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at hI ⊢
  refine hI.mono' ((hf.mul hg).aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [norm_mul]
  have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hw : legPIw x * legPIw x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
    rw [legPIw, ← Real.rpow_add' (by positivity) (by norm_num), Real.div_rpow h0 (by norm_num)]
    norm_num
  calc ‖f x‖ * ‖g x‖ ≤ (M * legPIw x) * (N * legPIw x) :=
        mul_le_mul (hfM x hx) (hgN x hx) (norm_nonneg _)
          (le_trans (norm_nonneg _) (hfM x hx))
    _ = M*N/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring


/-- `t ln t → 0`, so `t ln t = O(1)`, as `x → -1⁺`, `t = (1+x)/2`. -/
theorem legPI_tlogt_isBigO_left :
    (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) =O[𝓝[>] (-1:ℝ)] legPIw := by
  have h : Tendsto (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) (𝓝[>] (-1:ℝ)) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).comp
      (legPI_tendsto_half.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  exact (h.isBigO_one ℝ).trans legPI_one_isBigO_left

/-- `𝖯_α = O((1-x²)^{-1/4})` at `-1`. -/
theorem legPI_ferrersP_isBigO_left (α : ℂ) : ferrersP α 0 =O[𝓝[>] (-1:ℝ)] legPIw := by
  have h1 := (legPI_ferrersP_neg_one_isBigO α).trans legPI_tlogt_isBigO_left
  have h2 := (isBigO_ofReal_left.mpr legPI_log_isBigO_left).const_mul_left (legBdK (α+1) (-α))
  have h3 := ((isBigO_const_one ℝ (legBdK' (α+1) (-α) - 2 * Real.eulerMascheroniConstant *
    legBdK (α+1) (-α)) (𝓝[>] (-1:ℝ))).trans legPI_one_isBigO_left)
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- `𝖯_α = O((1-x²)^{-1/4})` at `1`. -/
theorem legPI_ferrersP_isBigO_right (α : ℂ) : ferrersP α 0 =O[𝓝[<] (1:ℝ)] legPIw :=
  ((legPI_tendsto_ferrersP_one α).isBigO_one ℝ).trans legPI_one_isBigO_right

theorem legPI_continuousOn_ferrersP (α : ℂ) : ContinuousOn (ferrersP α 0) (Ioo (-1) 1) :=
  fun _ hx => (legPI_continuousAt_ferrersP α hx.1).continuousWithinAt

/-- `𝖯_ν 𝖯_λ` is integrable on `[-1,1]`. -/
theorem legPI_intervalIntegrable_PP (ν lam : ℂ) :
    IntervalIntegrable (fun x => ferrersP ν 0 x * ferrersP lam 0 x) volume (-1) 1 := by
  obtain ⟨M, hM⟩ := legPI_bound (legPI_continuousOn_ferrersP ν) (legPI_ferrersP_isBigO_left ν)
    (legPI_ferrersP_isBigO_right ν)
  obtain ⟨N, hN⟩ := legPI_bound (legPI_continuousOn_ferrersP lam) (legPI_ferrersP_isBigO_left lam)
    (legPI_ferrersP_isBigO_right lam)
  exact legPI_intervalIntegrable_mul (legPI_continuousOn_ferrersP ν)
    (legPI_continuousOn_ferrersP lam) hM hN


section Constants
open DLMF.Gamma

/-- `Γ(s)⁻¹ = s Γ(s+1)⁻¹` for all `s`. -/
theorem legPI_recip_Gamma_eq (s : ℂ) : (Gamma s)⁻¹ = s * (Gamma (s+1))⁻¹ := by
  have := poch_mul_recip_Gamma_add_nat s 1
  rw [poch_one] at this
  simpa using this.symm

/-- Derivative of `Γ(s)⁻¹ = s Γ(s+1)⁻¹`: `(1/Γ)'(s) = 1/Γ(s+1) + s (1/Γ)'(s+1)`. -/
theorem legPI_recipGammaDeriv_rec (s : ℂ) :
    recipGammaDeriv 1 s = (Gamma (s+1))⁻¹ + s * recipGammaDeriv 1 (s+1) := by
  have hfun : (fun w : ℂ => (Gamma w)⁻¹) = fun w => w * (Gamma (w+1))⁻¹ :=
    funext legPI_recip_Gamma_eq
  have h1 := hasDerivAt_recip_Gamma' s
  rw [hfun] at h1
  have h2 : HasDerivAt (fun w : ℂ => w * (Gamma (w+1))⁻¹)
      (1 * (Gamma (s+1))⁻¹ + s * recipGammaDeriv 1 (s+1)) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_recip_Gamma' (s+1)).comp_add_const s 1)
  rw [h1.unique h2, one_mul]

/-- `K_{α+1} = -K_α` for the constant `K_α = 1/(Γ(α+1)Γ(-α))`. -/
theorem legPI_K_succ (α : ℂ) : legBdK (α+1+1) (-(α+1)) = -legBdK (α+1) (-α) := by
  unfold legBdK
  rw [legPI_recip_Gamma_eq (α+1), legPI_recip_Gamma_eq (-(α+1)), show -(α+1)+1 = -α by ring]
  ring

/-- `(α+1)(K'_{α+1} + K'_α) = 2K_α`. -/
theorem legPI_K'_succ (α : ℂ) :
    (α+1) * (legBdK' (α+1+1) (-(α+1)) + legBdK' (α+1) (-α)) = 2 * legBdK (α+1) (-α) := by
  unfold legBdK' legBdK
  have r1 := legPI_recipGammaDeriv_rec (-(α+1))
  have r2 := legPI_recipGammaDeriv_rec (α+1)
  have r3 := legPI_recip_Gamma_eq (α+1)
  have r4 := legPI_recip_Gamma_eq (-(α+1))
  rw [show -(α+1)+1 = -α by ring] at r1 r4
  linear_combination (α+1)*(Gamma (α+1+1))⁻¹ * r1 + (α+1)*recipGammaDeriv 1 (α+1+1) * r4 +
    ((α+1)*recipGammaDeriv 1 (-α) - 2*(Gamma (-α))⁻¹) * r3 + (α+1)*(Gamma (-α))⁻¹ * r2

/-- `π K_α = -sin(πα)`. -/
theorem legPI_K_eq (α : ℂ) : (π:ℂ) * legBdK (α+1) (-α) = -sin (π*α) := by
  have := legendre_recip_Gamma_reflection (-α)
  rw [show (1:ℂ) - -α = α+1 by ring, mul_neg, sin_neg] at this
  unfold legBdK; rw [← this]; ring

/-- `K'_α = cos(πα) - 2ψ(α+1)K_α` when `α+1` is not a pole. -/
theorem legPI_K'_eq {α : ℂ} (hα : ∀ m : ℕ, α+1 ≠ -(m:ℂ)) :
    legBdK' (α+1) (-α) = cos (π*α) - 2*digamma (α+1)*legBdK (α+1) (-α) := by
  have hr := legBd_reflection_deriv (-α)
  rw [show (1:ℂ) - -α = α+1 by ring, mul_neg, cos_neg] at hr
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := mul_left_cancel₀ hpi hr
  have hd := recipGammaDeriv_one_eq hα
  unfold legBdK' legBdK
  rw [← hr', hd]
  ring

end Constants


/-- `𝖯_α` solves the Legendre equation on `(-1,1)`. -/
theorem legPI_ferrersP_isFerrersSolution (α : ℂ) : IsFerrersSolution α 0 (ferrersP α 0) :=
  ((ferrersEven_isFerrersSolution α 0).add_smul (ferrersOdd_isFerrersSolution α 0) _ _).congr
    (ferrersP_eqOn_even_odd α 0).symm

/-- Green's identity for two order-zero Legendre solutions:
`((1-x²)(f g' - g f'))' = (ν(ν+1) - λ(λ+1)) f g`. -/
theorem legPI_green {ν lam : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν 0 f)
    (hg : IsFerrersSolution lam 0 g) {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y : ℝ => (1-(y:ℂ)^2)*(f y*deriv g y-g y*deriv f y))
      ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y := by
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at ef eg
  have hsq : HasDerivAt (fun y : ℝ => 1-(y:ℂ)^2) (-(2*(y:ℂ))) y := by
    have := ((hasDerivAt_id y).ofReal_comp.pow 2).const_sub 1
    simpa using this
  refine (hsq.mul ((hf1.hasDerivAt.mul hg2).sub (hg1.hasDerivAt.mul hf2))).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  linear_combination (f y)*eg-(g y)*ef

/-- The logarithmic coefficient `K_α = 1/(Γ(α+1)Γ(-α))` of `𝖯_α` at `-1`. -/
def legPIK (α : ℂ) : ℂ := legBdK (α+1) (-α)

/-- The constant term `C_α` of `𝖯_α` at `-1`. -/
def legPIC (α : ℂ) : ℂ :=
  legBdK' (α+1) (-α) - 2 * Real.eulerMascheroniConstant * legBdK (α+1) (-α)

/-- The polynomial remainder in the boundary form at `-1`. -/
def legPIR (Kn Kl Cn Cl rn rl n l : ℂ) (v : Fin 11 → ℂ) : ℂ :=
  (2*Kl*Kn*l - 2*Kl*Kn*n)*v 2 +
    (-2*Kl*l + 2*Kl*n)*v 7*v 0 +
    (-2*Kn*l + 2*Kn*n)*v 8*v 0 +
    (-2*Cl*Kn*l + 2*Cl*Kn*n - 2*Cn*Kl*l + 2*Cn*Kl*n)*v 1 +
    (2*l - 2*n)*v 0*v 3*v 4 +
    (2*Cl*l - 2*Cl*n)*v 0*v 3 +
    (2*Cn*l - 2*Cn*n)*v 0*v 4 +
    (2*Cl*Cn*l - 2*Cl*Cn*n)*v 0 +
    (-Kl*n - Kl)*v 7 +
    (Kn*l + Kn)*v 8 +
    (Kn*l + Kn)*v 9 +
    (-Kl*n - Kl)*v 10 +
    (-l + n)*v 3*v 4 +
    (-l - 1)*v 3*v 5 +
    (Cl*n + Cl - l*rl - rl)*v 3 +
    (n + 1)*v 4*v 6 +
    (-Cn*l - Cn + n*rn + rn)*v 4 +
    (-Cn*l - Cn)*v 5 +
    (Cl*n + Cl)*v 6

theorem legPI_continuous_R (Kn Kl Cn Cl rn rl n l : ℂ) : Continuous (legPIR Kn Kl Cn Cl rn rl n l) := by
  unfold legPIR; fun_prop

/-- The polynomial remainder in the boundary form at `+1`. -/
def legPIRp (kf kg cf cg rf rg n l : ℂ) (v : Fin 11 → ℂ) : ℂ :=
  (-2*kf*kg*l + 2*kf*kg*n)*v 2 +
    (2*kg*l - 2*kg*n)*v 7*v 0 +
    (2*kf*l - 2*kf*n)*v 8*v 0 +
    (2*cf*kg*l - 2*cf*kg*n + 2*cg*kf*l - 2*cg*kf*n)*v 1 +
    (-2*l + 2*n)*v 0*v 3*v 4 +
    (-2*cg*l + 2*cg*n)*v 0*v 3 +
    (-2*cf*l + 2*cf*n)*v 0*v 4 +
    (-2*cf*cg*l + 2*cf*cg*n)*v 0 +
    (kg*n + kg)*v 7 +
    (-kf*l - kf)*v 8 +
    (kf*l + kf)*v 9 +
    (-kg*n - kg)*v 10 +
    (l - n)*v 3*v 4 +
    (-l - 1)*v 3*v 5 +
    (-cg*n - cg - l*rg - rg)*v 3 +
    (n + 1)*v 4*v 6 +
    (cf*l + cf + n*rf + rf)*v 4 +
    (-cf*l - cf)*v 5 +
    (cg*n + cg)*v 6

theorem legPI_continuous_Rp (kf kg cf cg rf rg n l : ℂ) : Continuous (legPIRp kf kg cf cg rf rg n l) := by
  unfold legPIRp; fun_prop

/-- Basic limits at a boundary point where `τ → 0⁺`. -/
theorem legPI_basic_limits {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) :
    Tendsto (fun x => ((τ x : ℝ) : ℂ)) l (𝓝 0) ∧
    Tendsto (fun x => ((τ x : ℝ) : ℂ) * ((Real.log (τ x) : ℝ) : ℂ)) l (𝓝 0) ∧
    Tendsto (fun x => ((τ x : ℝ) : ℂ) * ((Real.log (τ x) : ℝ) : ℂ) * ((Real.log (τ x) : ℝ) : ℂ))
      l (𝓝 0) ∧
    Tendsto (fun x => τ x * Real.log (τ x)) l (𝓝 0) ∧
    Tendsto (fun x => Real.log (τ x) * (τ x * Real.log (τ x))) l (𝓝 0) := by
  have h1 : Tendsto (fun x => τ x * Real.log (τ x)) l (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).comp (hτ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun x => Real.log (τ x) * (τ x * Real.log (τ x))) l (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1/2) (by norm_num)).pow 2
    rw [show (0:ℝ)^2 = 0 by norm_num] at h
    refine (h.comp hτ).congr' ?_
    filter_upwards [hτ self_mem_nhdsWithin] with x (hx : 0 < τ x)
    have h2 : ((τ x)^(1/2:ℝ))^2 = τ x := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
    simp only [Function.comp_apply]
    rw [mul_pow, h2]; ring
  refine ⟨?_, ?_, ?_, h1, h2⟩
  · have := (continuous_ofReal.tendsto 0).comp (hτ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  · have := (continuous_ofReal.tendsto 0).comp h1
    simpa [Function.comp_def] using this
  · have := (continuous_ofReal.tendsto 0).comp h2
    have h3 : Tendsto (fun x => ((Real.log (τ x) : ℝ) : ℂ) * (((τ x : ℝ) : ℂ) *
        ((Real.log (τ x) : ℝ) : ℂ))) l (𝓝 0) := by simpa [Function.comp_def] using this
    exact h3.congr fun x => by ring

/-- `E → 0` and `ln τ · E → 0` when `E = O(τ ln τ)`. -/
theorem legPI_err_limits {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {E : ℝ → ℂ}
    (hE : E =O[l] (fun x => τ x * Real.log (τ x))) :
    Tendsto E l (𝓝 0) ∧ Tendsto (fun x => ((Real.log (τ x) : ℝ) : ℂ) * E x) l (𝓝 0) := by
  obtain ⟨-, -, -, h1, h2⟩ := legPI_basic_limits hτ
  refine ⟨hE.trans_tendsto h1, ?_⟩
  have hU : (fun x => ((Real.log (τ x) : ℝ) : ℂ)) =O[l] (fun x => Real.log (τ x)) :=
    isBigO_ofReal_left.mpr (isBigO_refl _ _)
  exact (hU.mul hE).trans_tendsto h2

/-- Limit of the Green boundary form at an endpoint `x = -1 + 2τ`, `τ → 0⁺`, for functions with
expansions `f = -k_f ln τ + c_f + O(τ ln τ)` etc. whose degree-shifted partners satisfy
`k_{f₁} = -k_f`, `c_{f₁} = -c_f + r_f`, `(ν+1) r_f = 2 k_f`. -/
theorem legPI_bdry_neg {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (hx : ∀ᶠ x : ℝ in l, (x:ℂ) = -1 + 2*τ x) {f g g1 f1 : ℝ → ℂ} {ν lam kf kg cf cg rf rg : ℂ}
    (hf : (fun x => f x + kf * Real.log (τ x) - cf) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg : (fun x => g x + kg * Real.log (τ x) - cg) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg1 : (fun x => g1 x - kg * Real.log (τ x) - (-cg + rg)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hf1 : (fun x => f1 x - kf * Real.log (τ x) - (-cf + rf)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hrg : (lam+1)*rg = 2*kg) (hrf : (ν+1)*rf = 2*kf) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) l
      (𝓝 (2*(kf*cg - kg*cf))) := by
  obtain ⟨cT, cTU, cTUU, -, -⟩ := legPI_basic_limits hτ
  obtain ⟨c1, d1⟩ := legPI_err_limits hτ hf
  obtain ⟨c2, d2⟩ := legPI_err_limits hτ hg
  obtain ⟨c3, d3⟩ := legPI_err_limits hτ hg1
  obtain ⟨c4, d4⟩ := legPI_err_limits hτ hf1
  set U : ℝ → ℂ := fun x => ((Real.log (τ x) : ℝ) : ℂ) with hU
  set V : ℝ → Fin 11 → ℂ := fun x => ![(τ x : ℂ), (τ x : ℂ) * U x, (τ x : ℂ) * U x * U x,
    f x + kf * U x - cf, g x + kg * U x - cg, g1 x - kg * U x - (-cg + rg),
    f1 x - kf * U x - (-cf + rf), U x * (f x + kf * U x - cf), U x * (g x + kg * U x - cg),
    U x * (g1 x - kg * U x - (-cg + rg)), U x * (f1 x - kf * U x - (-cf + rf))] with hV
  have cV : Tendsto V l (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · exact cT
    · exact cTU
    · exact cTUU
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have cR := ((legPI_continuous_R kf kg cf cg rf rg ν lam).tendsto 0).comp cV
  have hR0 : legPIR kf kg cf cg rf rg ν lam 0 = 0 := by simp [legPIR]
  rw [hR0] at cR
  have key := (tendsto_const_nhds (x := 2*(kf*cg - kg*cf))).add cR
  rw [add_zero] at key
  refine key.congr' ?_
  filter_upwards [hx] with x hx
  simp only [Function.comp_apply, hV, legPIR, Matrix.cons_val, hU]
  rw [hx]
  linear_combination (cf - kf*U x) * hrg - (cg - kg*U x) * hrf

/-- Limit of the Green boundary form at an endpoint `x = 1 - 2τ`, `τ → 0⁺`, for expansions with
`k_{f₁} = k_f`, `c_{f₁} = c_f + r_f`, `(ν+1) r_f = -2 k_f`. -/
theorem legPI_bdry_pos {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (hx : ∀ᶠ x : ℝ in l, (x:ℂ) = 1 - 2*τ x) {f g g1 f1 : ℝ → ℂ} {ν lam kf kg cf cg rf rg : ℂ}
    (hf : (fun x => f x + kf * Real.log (τ x) - cf) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg : (fun x => g x + kg * Real.log (τ x) - cg) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg1 : (fun x => g1 x + kg * Real.log (τ x) - (cg + rg)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hf1 : (fun x => f1 x + kf * Real.log (τ x) - (cf + rf)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hrg : (lam+1)*rg = -2*kg) (hrf : (ν+1)*rf = -2*kf) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) l
      (𝓝 (2*(kg*cf - kf*cg))) := by
  obtain ⟨cT, cTU, cTUU, -, -⟩ := legPI_basic_limits hτ
  obtain ⟨c1, d1⟩ := legPI_err_limits hτ hf
  obtain ⟨c2, d2⟩ := legPI_err_limits hτ hg
  obtain ⟨c3, d3⟩ := legPI_err_limits hτ hg1
  obtain ⟨c4, d4⟩ := legPI_err_limits hτ hf1
  set U : ℝ → ℂ := fun x => ((Real.log (τ x) : ℝ) : ℂ) with hU
  set V : ℝ → Fin 11 → ℂ := fun x => ![(τ x : ℂ), (τ x : ℂ) * U x, (τ x : ℂ) * U x * U x,
    f x + kf * U x - cf, g x + kg * U x - cg, g1 x + kg * U x - (cg + rg),
    f1 x + kf * U x - (cf + rf), U x * (f x + kf * U x - cf), U x * (g x + kg * U x - cg),
    U x * (g1 x + kg * U x - (cg + rg)), U x * (f1 x + kf * U x - (cf + rf))] with hV
  have cV : Tendsto V l (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · exact cT
    · exact cTU
    · exact cTUU
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have cR := ((legPI_continuous_Rp kf kg cf cg rf rg ν lam).tendsto 0).comp cV
  have hR0 : legPIRp kf kg cf cg rf rg ν lam 0 = 0 := by simp [legPIRp]
  rw [hR0] at cR
  have key := (tendsto_const_nhds (x := 2*(kg*cf - kf*cg))).add cR
  rw [add_zero] at key
  refine key.congr' ?_
  filter_upwards [hx] with x hx
  simp only [Function.comp_apply, hV, legPIRp, Matrix.cons_val, hU]
  rw [hx]
  linear_combination (cf - kf*U x) * hrg - (cg - kg*U x) * hrf

/-- `𝖰_ν(-x) = -cos(νπ) 𝖰_ν(x) - (π/2) sin(νπ) 𝖯_ν(x)` (DLMF 14.9.10 solved for `𝖰_ν(-x)`), valid
for every regular `ν`, integers included. -/
theorem legPI_ferrersQ_neg {ν : ℂ} (h : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν 0 (-x) = -cos (ν*π)*ferrersQ ν 0 x - π/2*sin (ν*π)*ferrersP ν 0 x := by
  have pyth := sin_sq_add_cos_sq (ν*π/2)
  rw [ferrersQ_even_odd, ferrersQ_even_odd, ferrersP_regular h hx, ferrersEven_neg, ferrersOdd_neg,
    legendre_sin_two_mul_half, legendre_cos_two_mul_half]
  simp only [add_zero, sub_zero, cpow_zero, one_mul]
  linear_combination (π:ℂ) * (Gamma ((ν+2)/2) * (Gamma ((ν+1)/2))⁻¹) * cos (ν*π/2) *
    ferrersOdd ν 0 x * pyth

/-- `𝖰_α` solves the Legendre equation on `(-1,1)`. -/
theorem legPI_ferrersQ_isFerrersSolution (α : ℂ) : IsFerrersSolution α 0 (ferrersQ α 0) :=
  ((ferrersEven_isFerrersSolution α 0).add_smul (ferrersOdd_isFerrersSolution α 0) _ _).congr
    (ferrersQ_eqOn_even_odd α 0).symm

theorem legPI_continuousOn_of_solution {α : ℂ} {f : ℝ → ℂ} (hf : IsFerrersSolution α 0 f) :
    ContinuousOn f (Ioo (-1) 1) :=
  fun y hy => (hf y hy).1.continuousAt.continuousWithinAt

theorem legPI_tendsto_half_right :
    Tendsto (fun x : ℝ => (1-x)/2) (𝓝[<] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => (1-x)/2) (𝓝 1) (𝓝 ((1-1)/2)) :=
      (tendsto_const_nhds.sub tendsto_id).div_const 2
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    simp only [mem_Ioi]; linarith

/-- `(1-x) ln(1-x) = O(τ ln τ)` with `τ = (1-x)/2`, as `x → 1⁻`. -/
theorem legPI_one_sub_log_isBigO :
    (fun x : ℝ => (1-x)*Real.log (1-x)) =O[𝓝[<] (1:ℝ)] (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
  have ht0 : 0 < (1-x)/2 := by linarith [hx.2]
  have ht1 : (1-x)/2 ≤ 1/2 := by linarith [hx.1]
  have hl2 : Real.log 2 ≤ |Real.log ((1-x)/2)| := by
    rw [abs_of_nonpos (Real.log_nonpos ht0.le (by linarith)), ← Real.log_inv]
    exact Real.log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) ht0]; linarith)
  have hL : (1-x)*Real.log (1-x) = 2*((1-x)/2)*(Real.log 2 + Real.log ((1-x)/2)) := by
    rw [← Real.log_mul (by norm_num) ht0.ne']; ring_nf
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hL, abs_mul, abs_mul, abs_mul, abs_of_pos ht0, abs_two]
  have h2 : |Real.log 2 + Real.log ((1-x)/2)| ≤ 2 * |Real.log ((1-x)/2)| := by
    calc _ ≤ |Real.log 2| + |Real.log ((1-x)/2)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos (Real.log_pos (by norm_num))]; linarith
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2*((1-x)/2))
  linarith

/-- DLMF 14.8.3 in the variable `τ = (1-x)/2`: `𝖰_α + ½ ln τ - (-γ - ψ(α+1)) = O(τ ln τ)`. -/
theorem legPI_ferrersQ_pos_isBigO {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ α 0 x + (1/2:ℂ) * Real.log ((1-x)/2) -
      (-Real.eulerMascheroniConstant - digamma (α+1))) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  refine ((legBd_ferrersQ_log_isBigO h).trans legPI_one_sub_log_isBigO).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
  have h1 : (0:ℝ) < 1 - x := by linarith [hx.2]
  have hl : log (2/(1-x):ℂ) = -(Real.log ((1-x)/2) : ℂ) := by
    rw [show (2/(1-x):ℂ) = ((2/(1-x):ℝ):ℂ) by push_cast; rfl, ← ofReal_log (by positivity),
      show 2/(1-x) = ((1-x)/2)⁻¹ by field_simp, Real.log_inv]
    push_cast; ring
  rw [hl]; ring

theorem legPI_tendsto_neg_left : Tendsto (fun x : ℝ => -x) (𝓝[>] (-1:ℝ)) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => -x) (𝓝 (-1)) (𝓝 (-(-1))) := tendsto_id.neg
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (-1)))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : -1 < x)
    simp only [mem_Iio]; linarith

/-- `𝖯_α - 1 = O(τ ln τ)` with `τ = (1-x)/2`, as `x → 1⁻`. -/
theorem legPI_ferrersP_pos_isBigO (α : ℂ) :
    (fun x : ℝ => ferrersP α 0 x + (0:ℂ) * Real.log ((1-x)/2) - 1) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  have hfun : ferrersP α 0 = fun y : ℝ => regularizedGaussHG (α+1) (-α) 1 ((1-(y:ℂ))/2) :=
    funext (legPI_ferrersP_zero α)
  have hw := legInt_half_mem_cutPlane (show (-1:ℝ) < 1 by norm_num)
  have hd : DifferentiableAt ℝ (ferrersP α 0) 1 := by
    rw [hfun]
    exact ((differentiableAt_regularizedGaussHG _ _ _ hw).restrictScalars ℝ).comp (1:ℝ)
      (by fun_prop)
  have h1 := hd.isBigO_sub.mono (nhdsWithin_le_nhds (s := Iio (1:ℝ)))
  rw [legPI_ferrersP_one] at h1
  have h2 : (fun x : ℝ => x - 1) =O[𝓝[<] (1:ℝ)] (fun x : ℝ => (((1-x)/2 : ℝ) : ℂ)) := by
    refine Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_two, abs_sub_comm]
    linarith [abs_nonneg (1-x)]
  have h3 := legBd_isBigO_self_mul_log.comp_tendsto legPI_tendsto_half_right
  refine (h1.trans (h2.trans h3)).congr_left fun x => ?_
  ring

/-- `𝖰_α` at `-1`: `𝖰_α - ½cos(απ) ln τ - c = O(τ ln τ)`, `τ = (1+x)/2`, with
`c = cos(απ)(γ + ψ(α+1)) - (π/2) sin(απ)`. -/
theorem legPI_ferrersQ_neg_isBigO {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ α 0 x + (-(1/2)*cos (α*π)) * Real.log ((1+x)/2) -
      (-cos (α*π)*(-Real.eulerMascheroniConstant - digamma (α+1)) - π/2*sin (α*π))) =O[𝓝[>] (-1:ℝ)]
      (fun x => (1+x)/2 * Real.log ((1+x)/2)) := by
  have hQ := (legPI_ferrersQ_pos_isBigO h).comp_tendsto legPI_tendsto_neg_left
  have hP := (legPI_ferrersP_pos_isBigO α).comp_tendsto legPI_tendsto_neg_left
  have hc := (hQ.const_mul_left (-cos (α*π))).add (hP.const_mul_left (-(π/2*sin (α*π))))
  have hr : (fun x : ℝ => (1-(-x))/2 * Real.log ((1-(-x))/2)) =
      (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) := by
    funext x; ring_nf
  simp only [Function.comp_def] at hc
  rw [hr] at hc
  refine hc.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hq := legPI_ferrersQ_neg h hx'
  rw [neg_neg] at hq
  rw [hq, show (1-(-x))/2 = (1+x)/2 by ring]
  ring

/-- `τ ln τ = O((1-x²)^{-1/4})` along any filter on which `τ → 0⁺`. -/
theorem legPI_tlogt_isBigO_w {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (h1 : (fun _ : ℝ => (1:ℝ)) =O[l] legPIw) :
    (fun x => τ x * Real.log (τ x)) =O[l] legPIw :=
  (((legPI_basic_limits hτ).2.2.2.1).isBigO_one ℝ).trans h1

/-- `𝖰_α = O((1-x²)^{-1/4})` at `1`. -/
theorem legPI_ferrersQ_isBigO_right {α : ℂ} (h : LegendreQRegular α 0) :
    ferrersQ α 0 =O[𝓝[<] (1:ℝ)] legPIw := by
  have h1 := (legPI_ferrersQ_pos_isBigO h).trans
    (legPI_tlogt_isBigO_w legPI_tendsto_half_right legPI_one_isBigO_right)
  have h2 := (isBigO_ofReal_left.mpr legPI_log_isBigO_right).const_mul_left (1/2:ℂ)
  have h3 := (isBigO_const_one ℝ (-Real.eulerMascheroniConstant - digamma (α+1) : ℂ)
    (𝓝[<] (1:ℝ))).trans legPI_one_isBigO_right
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- `𝖰_α = O((1-x²)^{-1/4})` at `-1`. -/
theorem legPI_ferrersQ_isBigO_left {α : ℂ} (h : LegendreQRegular α 0) :
    ferrersQ α 0 =O[𝓝[>] (-1:ℝ)] legPIw := by
  have h1 := (legPI_ferrersQ_neg_isBigO h).trans legPI_tlogt_isBigO_left
  have h2 := (isBigO_ofReal_left.mpr legPI_log_isBigO_left).const_mul_left (-(1/2)*cos (α*π))
  have h3 := (isBigO_const_one ℝ (-cos (α*π)*(-Real.eulerMascheroniConstant - digamma (α+1)) -
    π/2*sin (α*π) : ℂ) (𝓝[>] (-1:ℝ))).trans legPI_one_isBigO_left
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- Constant term of `𝖰_α` at `+1` (in the variable `τ = (1-x)/2`). -/
def legPIcpos (α : ℂ) : ℂ := -Real.eulerMascheroniConstant - digamma (α+1)

/-- Constant term of `𝖰_α` at `-1` (in the variable `τ = (1+x)/2`). -/
def legPIcneg (α : ℂ) : ℂ := -cos (α*π)*legPIcpos α - π/2*sin (α*π)

theorem legPI_regular_succ {α : ℂ} (h : LegendreQRegular α 0) : LegendreQRegular (α+1) 0 :=
  fun n hn => h (n+1) (by push_cast; linear_combination hn)

theorem legPI_regular_ne {α : ℂ} (h : LegendreQRegular α 0) : α + 1 ≠ 0 :=
  fun h' => h 0 (by push_cast; linear_combination h')

theorem legPI_regular_arg {α : ℂ} (h : LegendreQRegular α 0) : ∀ m : ℕ, α+1 ≠ -(m:ℂ) :=
  fun m hm => h m (by linear_combination hm)

theorem legPI_cpos_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (α+1)*(legPIcpos (α+1) - legPIcpos α) = -1 := by
  unfold legPIcpos
  rw [Complex.digamma_apply_add_one (α+1) (legPI_regular_arg h)]
  have := legPI_regular_ne h
  field_simp; ring

theorem legPI_cneg_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (α+1)*(legPIcneg (α+1) + legPIcneg α) = -cos (α*π) := by
  have hc := legPI_cpos_succ h
  unfold legPIcneg
  rw [show (α+1)*π = α*π + π by ring, cos_add_pi, sin_add_pi]
  linear_combination cos (α*π) * hc

/-- Green's identity on `[-1,1]` for two order-zero solutions obeying the recurrence 14.10.4, in
terms of the limits of the boundary form at `±1`. -/
theorem legPI_integral_green {f g f1 g1 : ℝ → ℂ} {ν lam Bm Bp : ℂ}
    (hf : IsFerrersSolution ν 0 f) (hg : IsFerrersSolution lam 0 g)
    (hrf : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv f x = (ν+1)*(x*f x - f1 x))
    (hrg : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv g x = (lam+1)*(x*g x - g1 x))
    (hint : IntervalIntegrable (fun x => f x * g x) volume (-1) 1)
    (hm : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      (𝓝[>] (-1)) (𝓝 Bm))
    (hp : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      (𝓝[<] 1) (𝓝 Bp))
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, f x * g x) = (Bp - Bm) / (ν*(ν+1) - lam*(lam+1)) := by
  set F : ℝ → ℂ := fun y => (1-(y:ℂ)^2)*(f y*deriv g y - g y*deriv f y) with hF
  have hd : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y :=
    fun y hy => legPI_green hf hg hy
  have hint' := hint.const_mul (ν*(ν+1) - lam*(lam+1))
  have hB : ∀ y ∈ Ioo (-1:ℝ) 1,
      (lam+1)*f y*(y*g y - g1 y) - (ν+1)*g y*(y*f y - f1 y) = F y := by
    intro y hy
    simp only [hF]
    linear_combination -(f y * hrg y hy) + g y * hrf y hy
  have ha := hm.congr' (by
    filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with y hy using hB y hy)
  have hb := hp.congr' (by
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with y hy using hB y hy)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) hd hint' ha hb
  rw [intervalIntegral.integral_const_mul] at hI
  rw [eq_div_iff hc, ← hI]; ring

theorem legPI_hx_neg : ∀ᶠ x : ℝ in 𝓝[>] (-1:ℝ), (x:ℂ) = -1 + 2*(((1+x)/2 : ℝ) : ℂ) :=
  Eventually.of_forall fun x => by push_cast; ring

theorem legPI_hx_pos : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), (x:ℂ) = 1 - 2*(((1-x)/2 : ℝ) : ℂ) :=
  Eventually.of_forall fun x => by push_cast; ring

/-- Expansion of `𝖰_{α+1}` at `-1` in the shape required by `legPI_bdry_neg`. -/
theorem legPI_ferrersQ_neg_isBigO_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ (α+1) 0 x - (-(1/2)*cos (α*π)) * Real.log ((1+x)/2) -
      (-legPIcneg α + (legPIcneg (α+1) + legPIcneg α))) =O[𝓝[>] (-1:ℝ)]
      (fun x => (1+x)/2 * Real.log ((1+x)/2)) := by
  refine (legPI_ferrersQ_neg_isBigO (legPI_regular_succ h)).congr_left fun x => ?_
  unfold legPIcneg legPIcpos
  rw [show (α+1)*π = α*π + π by ring, cos_add_pi, sin_add_pi]
  ring

/-- Expansion of `𝖰_{α+1}` at `+1` in the shape required by `legPI_bdry_pos`. -/
theorem legPI_ferrersQ_pos_isBigO_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ (α+1) 0 x + (1/2:ℂ) * Real.log ((1-x)/2) -
      (legPIcpos α + (legPIcpos (α+1) - legPIcpos α))) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  refine (legPI_ferrersQ_pos_isBigO (legPI_regular_succ h)).congr_left fun x => ?_
  unfold legPIcpos; ring

theorem legPI_ferrersQ_rec {α : ℂ} (h : LegendreQRegular α 0) :
    ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv (ferrersQ α 0) x =
      (α+1)*(x*ferrersQ α 0 x - ferrersQ (α+1) 0 x) := fun x hx => by
  rw [ferrersQ_recurrence_4 α 0 h hx]; ring

theorem legPI_ferrersP_rec (α : ℂ) :
    ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv (ferrersP α 0) x =
      (α+1)*(x*ferrersP α 0 x - ferrersP (α+1) 0 x) := fun x hx => by
  rw [ferrersP_recurrence_4 α 0 hx]; ring

theorem legPI_intervalIntegrable_QQ {ν lam : ℂ} (hν : LegendreQRegular ν 0)
    (hlam : LegendreQRegular lam 0) :
    IntervalIntegrable (fun x => ferrersQ ν 0 x * ferrersQ lam 0 x) volume (-1) 1 := by
  have c1 := legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution ν)
  have c2 := legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution lam)
  obtain ⟨M, hM⟩ := legPI_bound c1 (legPI_ferrersQ_isBigO_left hν) (legPI_ferrersQ_isBigO_right hν)
  obtain ⟨N, hN⟩ := legPI_bound c2 (legPI_ferrersQ_isBigO_left hlam)
    (legPI_ferrersQ_isBigO_right hlam)
  exact legPI_intervalIntegrable_mul c1 c2 hM hN

theorem legPI_intervalIntegrable_PQ {lam : ℂ} (ν : ℂ) (hlam : LegendreQRegular lam 0) :
    IntervalIntegrable (fun x => ferrersP ν 0 x * ferrersQ lam 0 x) volume (-1) 1 := by
  have c2 := legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution lam)
  obtain ⟨M, hM⟩ := legPI_bound (legPI_continuousOn_ferrersP ν) (legPI_ferrersP_isBigO_left ν)
    (legPI_ferrersP_isBigO_right ν)
  obtain ⟨N, hN⟩ := legPI_bound c2 (legPI_ferrersQ_isBigO_left hlam)
    (legPI_ferrersQ_isBigO_right hlam)
  exact legPI_intervalIntegrable_mul (legPI_continuousOn_ferrersP ν) c2 hM hN

/-- The Green integral of `𝖰_ν 𝖰_λ`. -/
theorem legPI_integral_QQ {ν lam : ℂ} (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0)
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, ferrersQ ν 0 x * ferrersQ lam 0 x) =
      (2*((1/2)*legPIcpos ν - (1/2)*legPIcpos lam) -
        2*((-(1/2)*cos (ν*π))*legPIcneg lam - (-(1/2)*cos (lam*π))*legPIcneg ν)) /
        (ν*(ν+1) - lam*(lam+1)) := by
  refine legPI_integral_green (legPI_ferrersQ_isFerrersSolution ν)
    (legPI_ferrersQ_isFerrersSolution lam) (legPI_ferrersQ_rec hν) (legPI_ferrersQ_rec hlam)
    (legPI_intervalIntegrable_QQ hν hlam) ?_ ?_ hc
  · refine legPI_bdry_neg legPI_tendsto_half legPI_hx_neg (legPI_ferrersQ_neg_isBigO hν)
      (legPI_ferrersQ_neg_isBigO hlam) (legPI_ferrersQ_neg_isBigO_succ hlam)
      (legPI_ferrersQ_neg_isBigO_succ hν) ?_ ?_
    · rw [legPI_cneg_succ hlam]; ring
    · rw [legPI_cneg_succ hν]; ring
  · refine legPI_bdry_pos legPI_tendsto_half_right legPI_hx_pos (legPI_ferrersQ_pos_isBigO hν)
      (legPI_ferrersQ_pos_isBigO hlam) (legPI_ferrersQ_pos_isBigO_succ hlam)
      (legPI_ferrersQ_pos_isBigO_succ hν) ?_ ?_
    · rw [legPI_cpos_succ hlam]; ring
    · rw [legPI_cpos_succ hν]; ring

/-- Expansion of `𝖯_{α+1}` at `-1` in the shape required by `legPI_bdry_neg`. -/
theorem legPI_ferrersP_neg_one_isBigO_succ (α : ℂ) :
    (fun x : ℝ => ferrersP (α+1) 0 x - legPIK α * Real.log ((1+x)/2) -
      (-legPIC α + (legBdK' (α+1+1) (-(α+1)) + legBdK' (α+1) (-α)))) =O[𝓝[>] (-1:ℝ)]
      (fun x => (1+x)/2 * Real.log ((1+x)/2)) := by
  refine (legPI_ferrersP_neg_one_isBigO (α+1)).congr_left fun x => ?_
  have hK := legPI_K_succ α
  unfold legPIC legPIK
  rw [hK]; ring

/-- Expansion of `𝖯_{α+1}` at `+1` in the shape required by `legPI_bdry_pos`. -/
theorem legPI_ferrersP_pos_isBigO_succ (α : ℂ) :
    (fun x : ℝ => ferrersP (α+1) 0 x + (0:ℂ) * Real.log ((1-x)/2) - (1 + 0)) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) :=
  (legPI_ferrersP_pos_isBigO (α+1)).congr_left fun x => by ring

/-- The Green integral of `𝖯_ν 𝖰_λ`. -/
theorem legPI_integral_PQ {ν lam : ℂ} (hlam : LegendreQRegular lam 0)
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersQ lam 0 x) =
      (2*((1/2)*1 - 0*legPIcpos lam) -
        2*(legPIK ν * legPIcneg lam - (-(1/2)*cos (lam*π)) * legPIC ν)) /
        (ν*(ν+1) - lam*(lam+1)) := by
  refine legPI_integral_green (legPI_ferrersP_isFerrersSolution ν)
    (legPI_ferrersQ_isFerrersSolution lam) (legPI_ferrersP_rec ν) (legPI_ferrersQ_rec hlam)
    (legPI_intervalIntegrable_PQ ν hlam) ?_ ?_ hc
  · refine legPI_bdry_neg legPI_tendsto_half legPI_hx_neg (legPI_ferrersP_neg_one_isBigO ν)
      (legPI_ferrersQ_neg_isBigO hlam) (legPI_ferrersQ_neg_isBigO_succ hlam)
      (legPI_ferrersP_neg_one_isBigO_succ ν) ?_ (legPI_K'_succ ν)
    rw [legPI_cneg_succ hlam]; ring
  · refine legPI_bdry_pos legPI_tendsto_half_right legPI_hx_pos (legPI_ferrersP_pos_isBigO ν)
      (legPI_ferrersQ_pos_isBigO hlam) (legPI_ferrersQ_pos_isBigO_succ hlam)
      (legPI_ferrersP_pos_isBigO_succ ν) ?_ ?_
    · rw [legPI_cpos_succ hlam]; ring
    · ring

theorem legPI_regular_of_re_pos {α : ℂ} (h : 0 < α.re) : LegendreQRegular α 0 := by
  intro n hn
  have := congrArg Complex.re hn
  simp at this
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- The Green integral of `𝖯_ν 𝖯_λ` on `[-1,1]` in terms of the boundary constants, for all `ν, λ`
with `(ν-λ)(ν+λ+1) ≠ 0`. -/
theorem legPI_integral_PP (ν lam : ℂ) (h : (ν*(ν+1) - lam*(lam+1)) ≠ 0) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x) =
      -(2*(legPIK ν * legPIC lam - legPIK lam * legPIC ν)) / (ν*(ν+1) - lam*(lam+1)) := by
  rw [legPI_integral_green (legPI_ferrersP_isFerrersSolution ν)
    (legPI_ferrersP_isFerrersSolution lam) (legPI_ferrersP_rec ν) (legPI_ferrersP_rec lam)
    (legPI_intervalIntegrable_PP ν lam)
    (legPI_bdry_neg legPI_tendsto_half legPI_hx_neg (legPI_ferrersP_neg_one_isBigO ν)
      (legPI_ferrersP_neg_one_isBigO lam) (legPI_ferrersP_neg_one_isBigO_succ lam)
      (legPI_ferrersP_neg_one_isBigO_succ ν) (legPI_K'_succ lam) (legPI_K'_succ ν))
    (legPI_bdry_pos legPI_tendsto_half_right legPI_hx_pos (legPI_ferrersP_pos_isBigO ν)
      (legPI_ferrersP_pos_isBigO lam) (legPI_ferrersP_pos_isBigO_succ lam)
      (legPI_ferrersP_pos_isBigO_succ ν) (by ring) (by ring)) h]
  unfold legPIC legPIK
  ring

/-- Closed form of the boundary constant `K_ν C_λ - K_λ C_ν`. -/
theorem legPI_boundary_const {ν lam : ℂ} (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    (π:ℂ)^2 * (legPIK ν * legPIC lam - legPIK lam * legPIC ν) =
      π*sin ((lam-ν)*π) + 2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1)) := by
  have hr : ∀ {α : ℂ}, LegendreQRegular α 0 → ∀ m : ℕ, α+1 ≠ -(m:ℂ) := by
    intro α hα m hm
    exact hα m (by linear_combination hm)
  have e1 := legPI_K'_eq (hr hν)
  have e2 := legPI_K'_eq (hr hlam)
  have k1 := legPI_K_eq ν
  have k2 := legPI_K_eq lam
  unfold legPIC legPIK
  rw [e1, e2]
  rw [show (lam-ν)*π = π*lam - π*ν by ring, sin_sub, mul_comm ν, mul_comm lam]
  linear_combination ((π:ℂ)*cos (π*lam) + 2*(digamma (ν+1) - digamma (lam+1))*π*
      legBdK (lam+1) (-lam)) * k1 +
    (-(π:ℂ)*cos (π*ν) - 2*(digamma (ν+1) - digamma (lam+1))*sin (π*ν)) * k2

/-- `K'_α = cos(πα) + 2 (1/Γ)'(α+1)/Γ(-α)` for every `α`. -/
theorem legPI_K'_eq_all (α : ℂ) :
    legBdK' (α+1) (-α) = cos (π*α) + 2*(DLMF.Gamma.recipGammaDeriv 1 (α+1) * (Gamma (-α))⁻¹) := by
  have hr := legBd_reflection_deriv (-α)
  rw [show (1:ℂ) - -α = α+1 by ring, mul_neg, cos_neg] at hr
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := mul_left_cancel₀ hpi hr
  unfold legBdK'
  rw [← hr']
  ring

/-- Closed form of the boundary constant for all degrees, with `S(α) = π (1/Γ)'(α+1)/Γ(-α)`
(the removable extension of `sin(πα) ψ(α+1)`). -/
theorem legPI_boundary_const_all (ν lam : ℂ) :
    (π:ℂ)^2 * (legPIK ν * legPIC lam - legPIK lam * legPIC ν) =
      π*sin ((lam-ν)*π) + 2*(sin (π*lam) * (π * DLMF.Gamma.recipGammaDeriv 1 (ν+1) * (Gamma (-ν))⁻¹) -
        sin (π*ν) * (π * DLMF.Gamma.recipGammaDeriv 1 (lam+1) * (Gamma (-lam))⁻¹)) := by
  have e1 := legPI_K'_eq_all ν
  have e2 := legPI_K'_eq_all lam
  have k1 := legPI_K_eq ν
  have k2 := legPI_K_eq lam
  unfold legPIC legPIK
  rw [e1, e2]
  rw [show (lam-ν)*π = π*lam - π*ν by ring, sin_sub]
  linear_combination ((π:ℂ)*cos (π*lam) + 2*π*(DLMF.Gamma.recipGammaDeriv 1 (lam+1) * (Gamma (-lam))⁻¹)) * k1 +
    (-(π:ℂ)*cos (π*ν) - 2*π*(DLMF.Gamma.recipGammaDeriv 1 (ν+1) * (Gamma (-ν))⁻¹)) * k2

/-! ### Parameter-uniform bounds and diagonal integrals

The zero-balanced expansion `legBd_zeroBalanced_eq` (DLMF 15.8.10 at `m = 0`) holds with a
remainder `legBdZbH` that is bounded uniformly in the parameters (Cauchy's estimate in the third
parameter, `legPIU_bound_H`). This gives `𝖯_λ, 𝖰_λ = O((1-x²)^{-1/4})` on `(-1,1)` uniformly for
`λ` near `ν`, and dominated convergence turns the off-diagonal integrals 14.17.10, 12, 14 into the
diagonal ones 14.17.11, 13, 15. Helper names carry the prefix `legPIU_`. -/



/-- Uniform bound for `𝐅(a,b;c;w)` on `‖a‖, ‖b‖, ‖c‖ ≤ R`, `‖w‖ ≤ 1/2`. -/
theorem legPIU_bound_F (R : ℝ) : ∃ M : ℝ, ∀ a b c w : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ‖c‖ ≤ R →
    ‖w‖ ≤ 1/2 → ‖regularizedGaussHGFun a b c w‖ ≤ M := by
  set S : Set (ℂ × ℂ × ℂ × ℂ) := Metric.closedBall 0 R ×ˢ (Metric.closedBall 0 R ×ˢ
    (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 (1/2)))
  have hS : IsCompact S := (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  have hsub : S ⊆ {q : ℂ × ℂ × ℂ × ℂ | q.2.2.2 ∈ cutPlane} := by
    rintro ⟨a, b, c, w⟩ ⟨-, -, -, hw⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hw
    show 1 - w ∈ slitPlane
    refine Or.inl ?_
    have := Complex.re_le_norm w
    simp only [sub_re, one_re]; linarith
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (differentiableOn_regularizedGaussHG_joint.continuousOn.mono hsub)
  refine ⟨M, fun a b c w ha hb hc hw => ?_⟩
  have hq : ((a, b, c, w) : ℂ × ℂ × ℂ × ℂ) ∈ S := by
    simp only [S, Set.mem_prod, Metric.mem_closedBall, dist_zero_right]
    exact ⟨ha, hb, hc, hw⟩
  have := hM _ hq
  rwa [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by linarith)] at this

/-- A continuous function is bounded on `‖a‖, ‖b‖ ≤ R`. -/
theorem legPIU_bound_two {f : ℂ × ℂ → ℂ} (hf : Continuous f) (R : ℝ) :
    ∃ M : ℝ, ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ‖f (a, b)‖ ≤ M := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0:ℂ) R).prod (isCompact_closedBall (0:ℂ) R)
    ).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun a b ha hb => hM _ (by
    simp only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right]; exact ⟨ha, hb⟩)⟩

/-- Uniform bound for the analytic part `H(a,b;w)` of DLMF 15.8.10 on `‖a‖, ‖b‖ ≤ R`,
`‖w‖ ≤ 1/2`, from Cauchy's estimate in the third parameter. -/
theorem legPIU_bound_H (R : ℝ) : ∃ M : ℝ, ∀ a b w : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R →
    ‖w‖ ≤ 1/2 → ‖legBdZbH a b w‖ ≤ M := by
  obtain ⟨MF, hMF⟩ := legPIU_bound_F (R+2)
  have cK : Continuous fun p : ℂ × ℂ => legBdK p.1 p.2 := by
    unfold legBdK
    exact (continuous_recip_Gamma.comp continuous_fst).mul (continuous_recip_Gamma.comp continuous_snd)
  have cK' : Continuous fun p : ℂ × ℂ => legBdK' p.1 p.2 := by
    unfold legBdK'
    have h1 := DLMF.Gamma.continuous_recipGammaDeriv 1
    exact ((h1.comp continuous_snd).mul (continuous_recip_Gamma.comp continuous_fst)).add
      ((continuous_recip_Gamma.comp continuous_snd).mul (h1.comp continuous_fst))
  obtain ⟨MK, hMK⟩ := legPIU_bound_two cK R
  obtain ⟨MK', hMK'⟩ := legPIU_bound_two cK' R
  refine ⟨MK * MF + MK' * MF + MK * MF, fun a b w ha hb hw => ?_⟩
  have hw1 : ‖w‖ < 1 := by linarith
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) ha
  have hMF0 : 0 ≤ MF := le_trans (norm_nonneg _) (hMF 0 0 0 0 (by simp; linarith)
    (by simp; linarith) (by simp; linarith) (by simp))
  have hK := hMK a b ha hb
  have hK' := hMK' a b ha hb
  -- first derivative
  have hd1 : ‖deriv (fun c => regularizedGaussHGFun a b (a+b-c+1) w) (a+b)‖ ≤ MF := by
    have hdiff : Differentiable ℂ (fun c => regularizedGaussHGFun a b (a+b-c+1) w) :=
      differentiable_regularizedGaussHGFun_of_differentiable (differentiable_const _)
        (differentiable_const _) ((differentiable_const _).sub differentiable_id |>.add_const 1) hw1
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := a+b) (R := 1) one_pos
      hdiff.diffContOnCl (C := MF) fun c hc => by
        rw [mem_sphere_iff_norm] at hc
        refine hMF _ _ _ _ (by linarith) (by linarith) ?_ hw
        calc ‖a+b-c+1‖ ≤ ‖a+b-c‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          _ = 2 := by rw [← norm_neg, neg_sub, hc]; simp; norm_num
          _ ≤ R+2 := by linarith
    simpa using this
  have hd2 : ‖deriv (fun c => regularizedGaussHGFun (c-a) (c-b) (c-a-b+1) w) (a+b)‖ ≤ MF := by
    have hdiff : Differentiable ℂ (fun c => regularizedGaussHGFun (c-a) (c-b) (c-a-b+1) w) :=
      differentiable_regularizedGaussHGFun_of_differentiable (differentiable_id.sub_const _)
        (differentiable_id.sub_const _) ((differentiable_id.sub_const _).sub_const _ |>.add_const 1) hw1
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := a+b) (R := 1) one_pos
      hdiff.diffContOnCl (C := MF) fun c hc => by
        rw [mem_sphere_iff_norm] at hc
        refine hMF _ _ _ _ ?_ ?_ ?_ hw
        · calc ‖c-a‖ = ‖(c-(a+b)) + b‖ := by ring_nf
            _ ≤ ‖c-(a+b)‖ + ‖b‖ := norm_add_le _ _
            _ ≤ R+2 := by linarith
        · calc ‖c-b‖ = ‖(c-(a+b)) + a‖ := by ring_nf
            _ ≤ ‖c-(a+b)‖ + ‖a‖ := norm_add_le _ _
            _ ≤ R+2 := by linarith
        · calc ‖c-a-b+1‖ = ‖(c-(a+b)) + 1‖ := by ring_nf
            _ ≤ ‖c-(a+b)‖ + ‖(1:ℂ)‖ := norm_add_le _ _
            _ ≤ R+2 := by simp; linarith
    simpa using this
  have hF1 : ‖regularizedGaussHGFun a b 1 w‖ ≤ MF :=
    hMF _ _ _ _ (by linarith) (by linarith) (by simp; linarith) hw
  unfold legBdZbH
  calc _ ≤ ‖legBdK a b * deriv (fun c => regularizedGaussHGFun a b (a+b-c+1) w) (a+b)‖ +
        ‖legBdK' a b * regularizedGaussHGFun a b 1 w‖ +
        ‖legBdK a b * deriv (fun c => regularizedGaussHGFun (c-a) (c-b) (c-a-b+1) w) (a+b)‖ :=
        norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ MK * MF + MK' * MF + MK * MF := by
      rw [norm_mul, norm_mul, norm_mul]
      gcongr <;> first | exact le_trans (norm_nonneg _) hK | exact le_trans (norm_nonneg _) hK'

/-- `𝖯_α(x) = O((1-x²)^{-1/4})` on `(-1,1)` uniformly for `‖α‖ ≤ R`: the parameter-uniform form of
DLMF 15.8.10 at `m = 0` used for diagonal integrals. -/
theorem legPIU_bound_P (R : ℝ) : ∃ M : ℝ, ∀ α : ℂ, ‖α‖ ≤ R → ∀ x ∈ Ioo (-1:ℝ) 1,
    ‖ferrersP α 0 x‖ ≤ M * legPIw x := by
  set R1 := |R| + 1
  obtain ⟨MF, hMF⟩ := legPIU_bound_F R1
  obtain ⟨MH, hMH⟩ := legPIU_bound_H R1
  have cK : Continuous fun p : ℂ × ℂ => legBdK p.1 p.2 := by
    unfold legBdK
    exact (continuous_recip_Gamma.comp continuous_fst).mul (continuous_recip_Gamma.comp continuous_snd)
  obtain ⟨MK, hMK⟩ := legPIU_bound_two cK R1
  set A := max MF 0
  set B := 4 * max MK 0 * max MF 0 + max MH 0
  refine ⟨A + B, fun α hα x hx => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have ha : ‖α+1‖ ≤ R1 := by
    calc ‖α+1‖ ≤ ‖α‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ R1 := by simp only [norm_one, R1]; linarith
  have hb : ‖-α‖ ≤ R1 := by rw [norm_neg]; simp only [R1]; linarith
  have hone : ‖(1:ℂ)‖ ≤ R1 := by simp only [norm_one, R1]; linarith [abs_nonneg R]
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := by positivity
  have hw1 := legPIw_one_le hx
  have hw0 := legPIw_pos hx
  rw [legPI_ferrersP_zero]
  by_cases hx0 : 0 ≤ x
  · have hn : ‖(1-(x:ℂ))/2‖ ≤ 1/2 := by
      rw [show (1-(x:ℂ))/2 = (((1-x)/2:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith [hx.2]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by linarith)]
    calc _ ≤ MF := hMF _ _ _ _ ha hb hone hn
      _ ≤ A := le_max_left _ _
      _ ≤ A + B := by linarith
      _ ≤ (A + B) * legPIw x := le_mul_of_one_le_right (by linarith) hw1
  · push Not at hx0
    set t : ℝ := (1+x)/2 with ht
    have ht0 : 0 < t := by simp only [t]; linarith [hx.1]
    have ht1 : t ≤ 1/2 := by simp only [t]; linarith
    have hz : (1-(x:ℂ))/2 = 1 - (t:ℂ) := by simp only [t]; push_cast; ring
    have hzn : ‖1 - (t:ℂ)‖ < 1 := by
      rw [show (1:ℂ) - t = ((1-t:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_lt]
      constructor <;> linarith
    have htn : ‖(1:ℂ) - (1 - (t:ℂ))‖ < 1 := by
      rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; linarith
    rw [hz, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzn,
      show regularizedGaussHGFun (α+1) (-α) 1 (1 - (t:ℂ)) =
        regularizedGaussHGFun (α+1) (-α) ((α+1) + -α) (1 - (t:ℂ)) by
          rw [show (α+1) + -α = (1:ℂ) by ring],
      legBd_zeroBalanced_eq _ _ hzn htn, sub_sub_cancel, ← Complex.ofReal_log ht0.le]
    have htn' : ‖(t:ℂ)‖ ≤ 1/2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
    have hF := hMF _ _ _ _ ha hb hone htn'
    have hH := hMH _ _ _ ha hb htn'
    have hK := hMK _ _ ha hb
    have hlog := legPI_abs_log_le ht0 (by linarith)
    have hp : 1 ≤ t^(-(1/4:ℝ)) := legPI_rpow_ge_one ht0 (by linarith)
    have hwt : t^(-(1/4:ℝ)) ≤ legPIw x := by
      rw [legPIw_eq hx]
      exact le_mul_of_one_le_right (Real.rpow_nonneg ht0.le _)
        (legPI_rpow_ge_one (by linarith [hx.2]) (by linarith [hx.1]))
    calc ‖-legBdK (α+1) (-α) * ((Real.log t : ℝ) : ℂ) * regularizedGaussHGFun (α+1) (-α) 1 (t:ℂ) +
          legBdZbH (α+1) (-α) (t:ℂ)‖
        ≤ ‖legBdK (α+1) (-α)‖ * |Real.log t| * ‖regularizedGaussHGFun (α+1) (-α) 1 (t:ℂ)‖ +
          ‖legBdZbH (α+1) (-α) (t:ℂ)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ max MK 0 * (4 * t^(-(1/4:ℝ))) * max MF 0 + max MH 0 := by
          gcongr
          · exact le_trans hK (le_max_left _ _)
          · exact le_trans hF (le_max_left _ _)
          · exact le_trans hH (le_max_left _ _)
      _ ≤ B * t^(-(1/4:ℝ)) := by
          simp only [B]
          nlinarith [le_max_right MK 0, le_max_right MF 0, le_max_right MH 0,
            mul_nonneg (le_max_right MK 0) (le_max_right MF 0)]
      _ ≤ (A + B) * legPIw x := by
          have := Real.rpow_nonneg ht0.le (-(1/4:ℝ))
          nlinarith

/-- `λ ↦ 𝖯_λ(x)` is entire for `x > -1`. -/
theorem legPIU_continuous_degree {x : ℝ} (hx : -1 < x) : Continuous fun α : ℂ => ferrersP α 0 x := by
  simp only [legPI_ferrersP_zero]
  exact (differentiable_regularizedGaussHG_comp (A := fun α : ℂ => α+1) (B := fun α : ℂ => -α)
    (C := fun _ => 1) (by fun_prop) (by fun_prop) (by fun_prop) (legInt_half_mem_cutPlane hx)).continuous

/-- Dominated convergence: `∫₋₁¹ 𝖯_ν 𝖯_λ → ∫₋₁¹ 𝖯_ν²` as `λ → ν`. -/
theorem legPIU_tendsto_PP (ν : ℂ) :
    Tendsto (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersP lam 0 x) (𝓝 ν)
      (𝓝 (∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersP ν 0 x)) := by
  obtain ⟨M, hM⟩ := legPIU_bound_P (‖ν‖ + 1)
  have hI := (legInt_intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul (M*M/4^(-1/2:ℝ))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => M*M/4^(-1/2:ℝ) * (1-x^2)^(-1/2:ℝ)) ?_ ?_ hI ?_
  · refine Eventually.of_forall fun lam => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact ((legPI_continuousAt_ferrersP ν hx.1).mul
      (legPI_continuousAt_ferrersP lam hx.1)).continuousWithinAt
  · have hb : ∀ᶠ lam in 𝓝 ν, ‖lam‖ ≤ ‖ν‖ + 1 := by
      filter_upwards [Metric.ball_mem_nhds ν one_pos] with lam hl
      rw [Metric.mem_ball, dist_eq_norm] at hl
      calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
        _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
        _ ≤ ‖ν‖ + 1 := by linarith
    filter_upwards [hb] with lam hl
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx'.1, hx'.2]
    have hw : legPIw x * legPIw x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
      rw [legPIw, ← Real.rpow_add' (by positivity) (by norm_num), Real.div_rpow h0 (by norm_num)]
      norm_num
    have h1 := hM ν (by linarith) x hx'
    have h2 := hM lam hl x hx'
    rw [norm_mul]
    calc ‖ferrersP ν 0 x‖ * ‖ferrersP lam 0 x‖ ≤ (M * legPIw x) * (M * legPIw x) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = M*M/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring
  · refine Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact tendsto_const_nhds.mul ((legPIU_continuous_degree hx.1).tendsto ν)

/-- Dominated convergence: `∫₋₁¹ 𝖯_λ² → ∫₋₁¹ 𝖯_ν²` as `λ → ν`. -/
theorem legPIU_tendsto_sq (ν : ℂ) :
    Tendsto (fun lam : ℂ => ∫ x : ℝ in -1..1, (ferrersP lam 0 x)^2) (𝓝 ν)
      (𝓝 (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)) := by
  obtain ⟨M, hM⟩ := legPIU_bound_P (‖ν‖ + 1)
  have hI := (legInt_intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul (M*M/4^(-1/2:ℝ))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => M*M/4^(-1/2:ℝ) * (1-x^2)^(-1/2:ℝ)) ?_ ?_ hI ?_
  · refine Eventually.of_forall fun lam => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact ((legPI_continuousAt_ferrersP lam hx.1).pow 2).continuousWithinAt
  · have hb : ∀ᶠ lam in 𝓝 ν, ‖lam‖ ≤ ‖ν‖ + 1 := by
      filter_upwards [Metric.ball_mem_nhds ν one_pos] with lam hl
      rw [Metric.mem_ball, dist_eq_norm] at hl
      calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
        _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
        _ ≤ ‖ν‖ + 1 := by linarith
    filter_upwards [hb] with lam hl
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx'.1, hx'.2]
    have hw : legPIw x * legPIw x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
      rw [legPIw, ← Real.rpow_add' (by positivity) (by norm_num), Real.div_rpow h0 (by norm_num)]
      norm_num
    have h2 := hM lam hl x hx'
    rw [norm_pow, pow_two]
    calc ‖ferrersP lam 0 x‖ * ‖ferrersP lam 0 x‖ ≤ (M * legPIw x) * (M * legPIw x) :=
          mul_le_mul h2 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h2)
      _ = M*M/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring
  · refine Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact ((legPIU_continuous_degree hx.1).tendsto ν).pow 2

/-- Uniform zero-balanced bound (DLMF 15.8.10 at `m = 0`):
`‖𝐅(a,b;a+b;1-t)‖ ≤ C t^{-1/4}` for `‖a‖, ‖b‖ ≤ R`, `0 < t ≤ 1/2`. -/
theorem legPIU_bound_zb (R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ∀ t : ℝ, 0 < t →
    t ≤ 1/2 → ‖regularizedGaussHGFun a b (a+b) (1 - (t:ℂ))‖ ≤ C * t^(-(1/4:ℝ)) := by
  set R1 := |R| + 1
  obtain ⟨MF, hMF⟩ := legPIU_bound_F R1
  obtain ⟨MH, hMH⟩ := legPIU_bound_H R1
  have cK : Continuous fun p : ℂ × ℂ => legBdK p.1 p.2 := by
    unfold legBdK
    exact (continuous_recip_Gamma.comp continuous_fst).mul (continuous_recip_Gamma.comp continuous_snd)
  obtain ⟨MK, hMK⟩ := legPIU_bound_two cK R1
  refine ⟨4 * max MK 0 * max MF 0 + max MH 0, by positivity, fun a b ha hb t ht0 ht1 => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have ha' : ‖a‖ ≤ R1 := by simp only [R1]; linarith
  have hb' : ‖b‖ ≤ R1 := by simp only [R1]; linarith
  have hone : ‖(1:ℂ)‖ ≤ R1 := by simp only [norm_one, R1]; linarith [abs_nonneg R]
  have hzn : ‖1 - (t:ℂ)‖ < 1 := by
    rw [show (1:ℂ) - t = ((1-t:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have htn : ‖(1:ℂ) - (1 - (t:ℂ))‖ < 1 := by
    rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; linarith
  rw [legBd_zeroBalanced_eq _ _ hzn htn, sub_sub_cancel, ← Complex.ofReal_log ht0.le]
  have htn' : ‖(t:ℂ)‖ ≤ 1/2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
  have hF := hMF _ _ _ _ ha' hb' hone htn'
  have hH := hMH _ _ _ ha' hb' htn'
  have hK := hMK _ _ ha' hb'
  have hlog := legPI_abs_log_le ht0 (by linarith)
  have hp : 1 ≤ t^(-(1/4:ℝ)) := legPI_rpow_ge_one ht0 (by linarith)
  calc ‖-legBdK a b * ((Real.log t : ℝ) : ℂ) * regularizedGaussHGFun a b 1 (t:ℂ) + legBdZbH a b (t:ℂ)‖
      ≤ ‖legBdK a b‖ * |Real.log t| * ‖regularizedGaussHGFun a b 1 (t:ℂ)‖ + ‖legBdZbH a b (t:ℂ)‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ max MK 0 * (4 * t^(-(1/4:ℝ))) * max MF 0 + max MH 0 := by
        gcongr
        · exact le_trans hK (le_max_left _ _)
        · exact le_trans hF (le_max_left _ _)
        · exact le_trans hH (le_max_left _ _)
    _ ≤ (4 * max MK 0 * max MF 0 + max MH 0) * t^(-(1/4:ℝ)) := by
        nlinarith [le_max_right MK 0, le_max_right MF 0, le_max_right MH 0,
          mul_nonneg (le_max_right MK 0) (le_max_right MF 0)]

/-- `‖𝐅(a,b;a+b;x²)‖ ≤ M (1-x²)^{-1/4}` on `(-1,1)`, uniformly for `‖a‖, ‖b‖ ≤ R`. -/
theorem legPIU_bound_sq (R : ℝ) : ∃ M : ℝ, ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ∀ x ∈ Ioo (-1:ℝ) 1,
    ‖regularizedGaussHG a b (a+b) ((x:ℂ)^2)‖ ≤ M * legPIw x := by
  obtain ⟨C, hC0, hC⟩ := legPIU_bound_zb R
  obtain ⟨MF, hMF⟩ := legPIU_bound_F (2*|R| + 1)
  refine ⟨max MF 0 + C, fun a b ha hb x hx => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have hw1 := legPIw_one_le hx
  have hx2 : x^2 < 1 := by nlinarith [hx.1, hx.2]
  have hsq : ((x:ℂ))^2 = ((x^2:ℝ):ℂ) := by push_cast; ring
  have hn : ‖((x:ℂ))^2‖ < 1 := by
    rw [hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]; exact hx2
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn]
  by_cases hx0 : x^2 ≤ 1/2
  · have hn' : ‖((x:ℂ))^2‖ ≤ 1/2 := by
      rw [hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]; exact hx0
    have hab : ‖a+b‖ ≤ 2*|R|+1 := by
      calc ‖a+b‖ ≤ ‖a‖+‖b‖ := norm_add_le _ _
        _ ≤ 2*|R|+1 := by linarith
    calc _ ≤ MF := hMF _ _ _ _ (by linarith [abs_nonneg R]) (by linarith [abs_nonneg R]) hab hn'
      _ ≤ max MF 0 + C := by linarith [le_max_left MF 0]
      _ ≤ (max MF 0 + C) * legPIw x :=
          le_mul_of_one_le_right (by linarith [le_max_right MF 0]) hw1
  · push Not at hx0
    set t : ℝ := 1 - x^2
    have ht0 : 0 < t := by simp only [t]; linarith
    have ht1 : t ≤ 1/2 := by simp only [t]; linarith
    rw [show ((x:ℂ))^2 = 1 - (t:ℂ) by simp only [t]; push_cast; ring]
    have hwt : t^(-(1/4:ℝ)) ≤ legPIw x := by
      rw [legPIw]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by simp only [t]; linarith) (by norm_num)
    calc _ ≤ C * t^(-(1/4:ℝ)) := hC a b ha hb t ht0 ht1
      _ ≤ (max MF 0 + C) * legPIw x := by
          have := Real.rpow_nonneg ht0.le (-(1/4:ℝ))
          nlinarith [le_max_right MF 0]

/-- A function continuous on a compact set is bounded there. -/
theorem legPIU_bound_on {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (hf : ContinuousOn f K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ‖f y‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  exact ⟨max B 0, le_max_right _ _, fun y hy => le_trans (hB y hy) (le_max_left _ _)⟩

/-- `𝖰_λ(x) = O((1-x²)^{-1/4})` on `(-1,1)` uniformly for `λ` near a regular `ν`. -/
theorem legPIU_bound_Q {ν : ℂ} (hν : LegendreQRegular ν 0) : ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ,
    ∀ lam : ℂ, ‖lam - ν‖ ≤ r → LegendreQRegular lam 0 ∧
      ∀ x ∈ Ioo (-1:ℝ) 1, ‖ferrersQ lam 0 x‖ ≤ M * legPIw x := by
  have hν1 := legHyp_nu hν
  have o : IsOpen {lam : ℂ | (Gamma (lam+0+1))⁻¹ ≠ 0} :=
    isOpen_ne_fun (continuous_recip_Gamma.comp (by fun_prop)) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp o ν (by simpa using inv_ne_zero (Gamma_ne_zero hν1))
  set r := ε/2
  have hr : 0 < r := by positivity
  set K := Metric.closedBall ν r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hreg : ∀ lam ∈ K, LegendreQRegular lam 0 := fun lam hl => legHyp_regular_of_recip (hball (by
    rw [Metric.mem_ball]; have := Metric.mem_closedBall.mp hl; simp only [r] at this; linarith))
  obtain ⟨B1, hB10, hB1⟩ := legPIU_bound_on (f := fun lam : ℂ => Gamma ((lam+0+1)/2)) hK
    (fun lam hl => (continuousAt_Gamma_ferrersQ (hreg lam hl)).1.continuousWithinAt)
  obtain ⟨B2, hB20, hB2⟩ := legPIU_bound_on (f := fun lam : ℂ => Gamma ((lam+0+2)/2)) hK
    (fun lam hl => (continuousAt_Gamma_ferrersQ (hreg lam hl)).2.continuousWithinAt)
  obtain ⟨B3, hB30, hB3⟩ := legPIU_bound_on (f := fun lam : ℂ => (Gamma ((lam-0+2)/2))⁻¹) hK
    (continuous_recip_Gamma.comp (by fun_prop)).continuousOn
  obtain ⟨B4, hB40, hB4⟩ := legPIU_bound_on (f := fun lam : ℂ => (Gamma ((lam-0+1)/2))⁻¹) hK
    (continuous_recip_Gamma.comp (by fun_prop)).continuousOn
  obtain ⟨B5, hB50, hB5⟩ := legPIU_bound_on (f := fun lam : ℂ => sin ((lam+0)*π/2)) hK
    (by fun_prop)
  obtain ⟨B6, hB60, hB6⟩ := legPIU_bound_on (f := fun lam : ℂ => cos ((lam+0)*π/2)) hK
    (by fun_prop)
  obtain ⟨MS, hMS⟩ := legPIU_bound_sq (‖ν‖ + r + 2)
  set MS' := max MS 0
  refine ⟨r, hr, (π/2) * (B5*B1*B3*MS' + B6*B2*B4*MS'), fun lam hl => ?_⟩
  have hlK : lam ∈ K := Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hl)
  refine ⟨hreg lam hlK, fun x hx => ?_⟩
  have hlam : ‖lam‖ ≤ ‖ν‖ + r := by
    calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
      _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hw0 := legPIw_pos hx
  have hxa : ‖(x:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2]
  -- the two hypergeometric factors
  have hE : ‖ferrersEven lam 0 x‖ ≤ MS' * legPIw x := by
    unfold ferrersEven
    rw [show -(lam+0)/2 = -lam/2 by ring, show (lam-0+1)/2 = (lam+1)/2 by ring, neg_zero, zero_div,
      cpow_zero, one_mul, show (1/2:ℂ) = -lam/2 + (lam+1)/2 by ring]
    refine le_trans (hMS _ _ ?_ ?_ x hx) (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0.le)
    · rw [norm_div, norm_neg]
      exact le_trans (div_le_self (norm_nonneg _) (by simp)) (by linarith)
    · calc ‖(lam+1)/2‖ ≤ ‖lam+1‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
        _ ≤ ‖lam‖ + 1 := by simpa using norm_add_le lam 1
        _ ≤ _ := by linarith
  have hO : ‖ferrersOdd lam 0 x‖ ≤ MS' * legPIw x := by
    unfold ferrersOdd
    rw [show (1-lam-0)/2 = (1-lam)/2 by ring, show (lam-0+2)/2 = (lam+2)/2 by ring, neg_zero, zero_div,
      cpow_zero, one_mul, show (3/2:ℂ) = (1-lam)/2 + (lam+2)/2 by ring, norm_mul]
    have h := hMS ((1-lam)/2) ((lam+2)/2) ?_ ?_ x hx
    · calc ‖(x:ℂ)‖ * _ ≤ 1 * (MS * legPIw x) := mul_le_mul hxa h (norm_nonneg _) zero_le_one
        _ ≤ MS' * legPIw x := by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hw0.le
    · calc ‖(1-lam)/2‖ ≤ ‖1-lam‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
        _ ≤ 1 + ‖lam‖ := by simpa using norm_sub_le (1:ℂ) lam
        _ ≤ _ := by linarith
    · calc ‖(lam+2)/2‖ ≤ ‖lam+2‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
        _ ≤ ‖lam‖ + 2 := by simpa using norm_add_le lam 2
        _ ≤ _ := by linarith
  rw [ferrersQ_even_odd, cpow_zero, one_mul]
  have hπ : ‖((π:ℂ))/2‖ = π/2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; simp
  rw [norm_mul, hπ]
  have e1 := hB1 lam hlK; have e2 := hB2 lam hlK; have e3 := hB3 lam hlK
  have e4 := hB4 lam hlK; have e5 := hB5 lam hlK; have e6 := hB6 lam hlK
  have hMS0 : 0 ≤ MS' := le_max_right _ _
  calc π/2 * ‖-sin ((lam+0)*π/2)*Gamma ((lam+0+1)/2)*(Gamma ((lam-0+2)/2))⁻¹*ferrersEven lam 0 x +
        cos ((lam+0)*π/2)*Gamma ((lam+0+2)/2)*(Gamma ((lam-0+1)/2))⁻¹*ferrersOdd lam 0 x‖
      ≤ π/2 * (B5*B1*B3*(MS' * legPIw x) + B6*B2*B4*(MS' * legPIw x)) := by
        gcongr
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_mul, norm_mul, norm_mul]
        gcongr
    _ = _ := by ring

/-- Dominated convergence on `(-1,1)` with the weight `(1-x²)^{-1/4}`. -/
theorem legPIU_tendsto_int {F : ℂ → ℝ → ℂ} {f : ℝ → ℂ} {ν : ℂ} {M N : ℝ}
    (hf : ContinuousOn f (Ioo (-1) 1)) (hfN : ∀ x ∈ Ioo (-1:ℝ) 1, ‖f x‖ ≤ N * legPIw x)
    (hFc : ∀ lam, ContinuousOn (F lam) (Ioo (-1) 1))
    (hFM : ∀ᶠ lam in 𝓝 ν, ∀ x ∈ Ioo (-1:ℝ) 1, ‖F lam x‖ ≤ M * legPIw x)
    (hlim : ∀ x ∈ Ioo (-1:ℝ) 1, ContinuousAt (fun lam => F lam x) ν) :
    Tendsto (fun lam => ∫ x in (-1:ℝ)..1, f x * F lam x) (𝓝 ν)
      (𝓝 (∫ x in (-1:ℝ)..1, f x * F ν x)) := by
  have hI := (legInt_intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul (N*M/4^(-1/2:ℝ))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => N*M/4^(-1/2:ℝ) * (1-x^2)^(-1/2:ℝ)) ?_ ?_ hI ?_
  · refine Eventually.of_forall fun lam => ?_
    rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1), ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (hf.mul (hFc lam)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [hFM] with lam hl
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx'.1, hx'.2]
    have hw : legPIw x * legPIw x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
      rw [legPIw, ← Real.rpow_add' (by positivity) (by norm_num), Real.div_rpow h0 (by norm_num)]
      norm_num
    have h1 := hfN x hx'
    have h2 := hl x hx'
    rw [norm_mul]
    calc ‖f x‖ * ‖F lam x‖ ≤ (N * legPIw x) * (M * legPIw x) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = N*M/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring
  · filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact tendsto_const_nhds.mul (hlim x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).tendsto

/-- ferrers product integral 10. -/
@[dlmf 14.17.E10]
theorem ferrers_product_integral_10 (ν : ℂ) (lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x)=2*(2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*sin ((lam-ν)*π))/(π^2*(lam-ν)*(lam+ν+1)) := by
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
  have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hB := legPI_boundary_const hν hlam
  rw [legPI_integral_PP ν lam hc, show 2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1))+
    π*sin ((lam-ν)*π) = (π:ℂ)^2 * (legPIK ν * legPIC lam - legPIK lam * legPIC ν) by
    rw [hB]; ring]
  field_simp
  ring

/-- ferrers product integral 11. -/
@[dlmf 14.17.E11]
theorem ferrers_product_integral_11 (ν : ℂ) (hν : ν ≠ -1/2) (hr : LegendreQRegular ν 0) :
    (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)=(π^2-2*(sin (ν*π))^2*deriv digamma (ν+1))/(π^2*(ν+1/2)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2ν : 2*ν+1 ≠ 0 := fun h => hν (by linear_combination h/2)
  have hν1 := legHyp_nu hr
  -- the off-diagonal formula near `ν`
  set N : ℂ → ℂ := fun lam => 2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*sin ((lam-ν)*π)
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hN : HasDerivAt N (2*sin (ν*π)*(cos (ν*π)*(1*π)*(digamma (ν+1)-digamma (ν+1)) +
      sin (ν*π)*(-deriv digamma (ν+1))) + π*(cos ((ν-ν)*π)*(1*π))) ν := by
    have hs := ((hasDerivAt_id' ν).mul_const (π:ℂ)).csin
    have hs2 := (((hasDerivAt_id' ν).sub_const ν).mul_const (π:ℂ)).csin
    have := ((hs.mul ((hasDerivAt_const ν (digamma (ν+1))).sub hψ')).const_mul (2*sin (ν*π))).add
      (hs2.const_mul (π:ℂ))
    simp only [Pi.mul_apply, Pi.sub_apply] at this
    convert this using 1
    · funext lam; simp only [N, Pi.add_apply]; ring
    · ring
  have hN0 : N ν = 0 := by simp [N]
  have hsl := hasDerivAt_iff_tendsto_slope.mp hN
  have hden : Tendsto (fun lam : ℂ => 2/(π^2*(lam+ν+1))) (𝓝[≠] ν) (𝓝 (2/(π^2*(ν+ν+1)))) := by
    refine ((continuousAt_const.div (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).add
      continuousAt_const)) ?_).tendsto).mono_left nhdsWithin_le_nhds
    exact mul_ne_zero (pow_ne_zero 2 hπ) (by show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν)
  have hR := hsl.mul hden
  -- eventually the off-diagonal identity holds
  have hreg : ∀ᶠ lam in 𝓝 ν, LegendreQRegular lam 0 := by
    have o : IsOpen {lam : ℂ | (Gamma (lam+0+1))⁻¹ ≠ 0} :=
      isOpen_ne_fun (continuous_recip_Gamma.comp (by fun_prop)) continuous_const
    filter_upwards [o.mem_nhds (by simpa using inv_ne_zero (Gamma_ne_zero hν1))] with lam h
    exact legHyp_regular_of_recip h
  have hne : ∀ᶠ lam in 𝓝 ν, lam ≠ -ν-1 :=
    continuousAt_id.eventually_ne (show ν ≠ -ν-1 from fun h => h2ν (by linear_combination h))
  have heq : (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersP lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope N ν lam * (2/(π^2*(lam+ν+1))) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hreg, nhdsWithin_le_nhds hne]
      with lam (h0 : lam ≠ ν) hl h1
    rw [ferrers_product_integral_10 ν lam h0 h1 hr hl, slope_def_field, hN0, sub_zero]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
    simp only [N]
    field_simp
  have hu := tendsto_nhds_unique (((legPIU_tendsto_PP ν).mono_left nhdsWithin_le_nhds).congr' heq) hR
  simp only [pow_two]
  rw [hu]
  have h3 : ν + 1/2 ≠ 0 := fun h => h2ν (by linear_combination 2*h)
  rw [show ν+ν+1 = 2*(ν+1/2) by ring, sub_self, sub_self, zero_mul, Complex.cos_zero]
  generalize ν + 1/2 = u at h3 ⊢
  field_simp
  ring

/-- ferrers product integral 12. -/
@[dlmf 14.17.E12]
theorem ferrers_product_integral_12 (ν : ℂ) (lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    (∫ x : ℝ in -1..1, ferrersQ ν 0 x*ferrersQ lam 0 x)=((digamma (ν+1)-digamma (lam+1))*(1+cos (ν*π)*cos (lam*π))+π/2*sin ((lam-ν)*π))/((lam-ν)*(lam+ν+1)) := by
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
  have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  rw [legPI_integral_QQ hν hlam hc, show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring,
    show (lam-ν)*π = lam*π - ν*π by ring, sin_sub]
  unfold legPIcneg legPIcpos
  field_simp
  ring

/-- ferrers product integral 13. -/
@[dlmf 14.17.E13]
theorem ferrers_product_integral_13 (ν : ℂ) (hν : ν ≠ -1/2) (hr : LegendreQRegular ν 0) :
    (∫ x : ℝ in -1..1, (ferrersQ ν 0 x)^2)=(π^2-2*(1+(cos (ν*π))^2)*deriv digamma (ν+1))/(2*(2*ν+1)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2ν : 2*ν+1 ≠ 0 := fun h => hν (by linear_combination h/2)
  have hν1 := legHyp_nu hr
  obtain ⟨r, hr0, M, hM⟩ := legPIU_bound_Q hr
  have hnear : ∀ᶠ lam in 𝓝 ν, ‖lam - ν‖ ≤ r := by
    filter_upwards [Metric.closedBall_mem_nhds ν hr0] with lam hl
    rwa [Metric.mem_closedBall, dist_eq_norm] at hl
  have hlimI := legPIU_tendsto_int (F := fun lam x => ferrersQ lam 0 x) (f := ferrersQ ν 0)
    (legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution ν))
    ((hM ν (by simp; linarith)).2)
    (fun lam => legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution lam))
    (by filter_upwards [hnear] with lam hl using (hM lam hl).2)
    (fun x hx => continuousAt_ferrersQ_degree hr hx)
  set N : ℂ → ℂ := fun lam => (digamma (ν+1)-digamma (lam+1))*(1+cos (ν*π)*cos (lam*π))+π/2*sin ((lam-ν)*π)
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hN : HasDerivAt N ((0 - deriv digamma (ν+1)) * (1+cos (ν*π)*cos (ν*π)) +
      (digamma (ν+1)-digamma (ν+1)) * (cos (ν*π) * (-sin (ν*π) * (1*π))) +
      π/2*(cos ((ν-ν)*π)*(1*π))) ν := by
    have hc := ((hasDerivAt_id' ν).mul_const (π:ℂ)).ccos
    have hs2 := (((hasDerivAt_id' ν).sub_const ν).mul_const (π:ℂ)).csin
    have := (((hasDerivAt_const ν (digamma (ν+1))).sub hψ').mul
      ((hasDerivAt_const ν (1:ℂ)).add (hc.const_mul (cos (ν*π))))).add (hs2.const_mul ((π:ℂ)/2))
    simp only [Pi.sub_apply, zero_add] at this
    convert this using 1
  have hN0 : N ν = 0 := by simp [N]
  have hsl := hasDerivAt_iff_tendsto_slope.mp hN
  have hden : Tendsto (fun lam : ℂ => 1/(lam+ν+1)) (𝓝[≠] ν) (𝓝 (1/(ν+ν+1))) := by
    refine ((continuousAt_const.div ((continuousAt_id.add continuousAt_const).add
      continuousAt_const) ?_).tendsto).mono_left nhdsWithin_le_nhds
    show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν
  have hR := hsl.mul hden
  have hne : ∀ᶠ lam in 𝓝 ν, lam ≠ -ν-1 :=
    continuousAt_id.eventually_ne (show ν ≠ -ν-1 from fun h => h2ν (by linear_combination h))
  have heq : (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersQ ν 0 x * ferrersQ lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope N ν lam * (1/(lam+ν+1)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hne]
      with lam (h0 : lam ≠ ν) hl h1
    rw [ferrers_product_integral_12 ν lam h0 h1 hr (hM lam hl).1, slope_def_field, hN0, sub_zero]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    have hd2 : lam + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
    simp only [N]
    field_simp
  have hu := tendsto_nhds_unique (((hlimI).mono_left nhdsWithin_le_nhds).congr' heq) hR
  simp only [pow_two]
  rw [hu]
  have h3 : ν + 1/2 ≠ 0 := fun h => h2ν (by linear_combination 2*h)
  rw [show ν+ν+1 = 2*(ν+1/2) by ring, show 2*ν+1 = 2*(ν+1/2) by ring]
  simp only [sub_self, zero_mul, Complex.cos_zero, add_zero, one_mul]
  generalize ν + 1/2 = u at h3 ⊢
  field_simp
  ring

/-- ferrers product integral 14. -/
@[dlmf 14.17.E14]
theorem ferrers_product_integral_14 (ν : ℂ) (lam : ℂ) (hν : 0 < ν.re) (hlam : 0 < lam.re) (hne : lam ≠ ν) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersQ lam 0 x)=(2*sin (ν*π)*cos (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*cos ((lam-ν)*π)-π)/(π*(lam-ν)*(lam+ν+1)) := by
  have hrν := legPI_regular_of_re_pos hν
  have hrl := legPI_regular_of_re_pos hlam
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr hne
  have hd2 : lam + ν + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hK : legBdK (ν+1) (-ν) = -sin (ν*π)/π := by
    rw [eq_div_iff hpi, mul_comm, legPI_K_eq ν, mul_comm]
  rw [legPI_integral_PQ hrl hc, show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring,
    show (lam-ν)*π = lam*π - ν*π by ring, cos_sub]
  unfold legPIcneg legPIcpos legPIC legPIK
  rw [legPI_K'_eq (legPI_regular_arg hrν), hK, show (π:ℂ)*ν = ν*π by ring]
  field_simp
  ring

/-- ferrers product integral 15. -/
@[dlmf 14.17.E15]
theorem ferrers_product_integral_15 (ν : ℂ) (hν : 0 < ν.re) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersQ ν 0 x)=-sin (2*ν*π)*deriv digamma (ν+1)/(π*(2*ν+1)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr := legPI_regular_of_re_pos hν
  have h2ν : 2*ν+1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hν1 := legHyp_nu hr
  obtain ⟨r, hr0, M, hM⟩ := legPIU_bound_Q hr
  obtain ⟨MP, hMP⟩ := legPIU_bound_P ‖ν‖
  have hnear : ∀ᶠ lam in 𝓝 ν, ‖lam - ν‖ ≤ r := by
    filter_upwards [Metric.closedBall_mem_nhds ν hr0] with lam hl
    rwa [Metric.mem_closedBall, dist_eq_norm] at hl
  have hlimI := legPIU_tendsto_int (F := fun lam x => ferrersQ lam 0 x) (f := ferrersP ν 0)
    (legPI_continuousOn_ferrersP ν) (hMP ν le_rfl)
    (fun lam => legPI_continuousOn_of_solution (legPI_ferrersQ_isFerrersSolution lam))
    (by filter_upwards [hnear] with lam hl using (hM lam hl).2)
    (fun x hx => continuousAt_ferrersQ_degree hr hx)
  set N : ℂ → ℂ := fun lam => 2*sin (ν*π)*cos (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*cos ((lam-ν)*π)-π
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hN : HasDerivAt N (2*sin (ν*π)*(-sin (ν*π)*(1*π)*(digamma (ν+1)-digamma (ν+1)) +
      cos (ν*π)*(0-deriv digamma (ν+1))) + π*(-sin ((ν-ν)*π)*(1*π))) ν := by
    have hc := ((hasDerivAt_id' ν).mul_const (π:ℂ)).ccos
    have hc2 := (((hasDerivAt_id' ν).sub_const ν).mul_const (π:ℂ)).ccos
    have := (((hc.mul ((hasDerivAt_const ν (digamma (ν+1))).sub hψ')).const_mul (2*sin (ν*π))).add
      (hc2.const_mul (π:ℂ))).sub_const (π:ℂ)
    simp only [Pi.mul_apply, Pi.sub_apply] at this
    convert this using 1
    funext lam; simp only [N, Pi.add_apply]; ring
  have hN0 : N ν = 0 := by simp [N]
  have hsl := hasDerivAt_iff_tendsto_slope.mp hN
  have hden : Tendsto (fun lam : ℂ => 1/(π*(lam+ν+1))) (𝓝[≠] ν) (𝓝 (1/(π*(ν+ν+1)))) := by
    refine ((continuousAt_const.div (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).add
      continuousAt_const)) ?_).tendsto).mono_left nhdsWithin_le_nhds
    exact mul_ne_zero hπ (by show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν)
  have hR := hsl.mul hden
  have hre : ∀ᶠ lam in 𝓝 ν, 0 < lam.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hν)
  have heq : (fun lam : ℂ => ∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersQ lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope N ν lam * (1/(π*(lam+ν+1))) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hre] with lam (h0 : lam ≠ ν) hl
    rw [ferrers_product_integral_14 ν lam hν hl h0, slope_def_field, hN0, sub_zero]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    have hd2 : lam + ν + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    simp only [N]
    field_simp
  have hu := tendsto_nhds_unique (((hlimI).mono_left nhdsWithin_le_nhds).congr' heq) hR
  rw [hu, show 2*ν*π = 2*(ν*π) by ring, Complex.sin_two_mul, sub_self, sub_self, zero_mul,
    Complex.sin_zero, neg_zero, zero_mul, mul_zero, zero_add, mul_zero, add_zero,
    show ν+ν+1 = 2*ν+1 by ring]
  field_simp
  ring

/-- Green's identity for two Legendre solutions of the same order `μ`. -/
theorem legPI_green_mu {ν lam μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (hg : IsFerrersSolution lam μ g) {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y : ℝ => (1-(y:ℂ)^2)*(f y*deriv g y-g y*deriv f y))
      ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y := by
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
  have hsq : HasDerivAt (fun y : ℝ => 1-(y:ℂ)^2) (-(2*(y:ℂ))) y := by
    have := ((hasDerivAt_id y).ofReal_comp.pow 2).const_sub 1
    simpa using this
  refine (hsq.mul ((hf1.hasDerivAt.mul hg2).sub (hg1.hasDerivAt.mul hf2))).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  linear_combination (f y)*eg-(g y)*ef

/-- Green's identity on `[-1,1]` for two solutions of the same order, in terms of the limits of a
function `B` equal to the boundary form `(1-x²)(f g' - g f')` on `(-1,1)`. -/
theorem legPI_integral_green_B {f g B : ℝ → ℂ} {ν lam μ Bm Bp : ℂ}
    (hf : IsFerrersSolution ν μ f) (hg : IsFerrersSolution lam μ g)
    (hB : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*(f x*deriv g x - g x*deriv f x) = B x)
    (hint : IntervalIntegrable (fun x => f x * g x) volume (-1) 1)
    (hm : Tendsto B (𝓝[>] (-1)) (𝓝 Bm)) (hp : Tendsto B (𝓝[<] 1) (𝓝 Bp))
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, f x * g x) = (Bp - Bm) / (ν*(ν+1) - lam*(lam+1)) := by
  set F : ℝ → ℂ := fun y => (1-(y:ℂ)^2)*(f y*deriv g y - g y*deriv f y) with hF
  have hd : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y :=
    fun y hy => legPI_green_mu hf hg hy
  have hint' := hint.const_mul (ν*(ν+1) - lam*(lam+1))
  have ha := hm.congr' (by
    filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with y hy using (hB y hy).symm)
  have hb := hp.congr' (by
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with y hy using (hB y hy).symm)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) hd hint' ha hb
  rw [intervalIntegral.integral_const_mul] at hI
  rw [eq_div_iff hc, ← hI]; ring

/-- `𝖯^μ_α` solves the associated Legendre equation on `(-1,1)`. -/
theorem legPI_ferrersP_isFerrersSolution_mu (α μ : ℂ) : IsFerrersSolution α μ (ferrersP α μ) :=
  ((ferrersEven_isFerrersSolution α μ).add_smul (ferrersOdd_isFerrersSolution α μ) _ _).congr
    (ferrersP_eqOn_even_odd α μ).symm

/-- `𝖰^μ_α` solves the associated Legendre equation on `(-1,1)`. -/
theorem legPI_ferrersQ_isFerrersSolution_mu (α μ : ℂ) : IsFerrersSolution α μ (ferrersQ α μ) :=
  ((ferrersEven_isFerrersSolution α μ).add_smul (ferrersOdd_isFerrersSolution α μ) _ _).congr
    (ferrersQ_eqOn_even_odd α μ).symm

/-- A solution of the associated Legendre equation is continuous on `(-1,1)`. -/
theorem legPI_continuousOn_of_solution' {α μ : ℂ} {f : ℝ → ℂ} (hf : IsFerrersSolution α μ f) :
    ContinuousOn f (Ioo (-1) 1) :=
  fun y hy => (hf y hy).1.continuousAt.continuousWithinAt

/-- `(k+1)_j · k! = (k+j)!`. -/
theorem legPI_poch_nat (k j : ℕ) : poch ((k:ℂ)+1) j * (k.factorial : ℂ) = ((k+j).factorial : ℂ) := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih =>
    rw [poch_succ, mul_right_comm, ih, show k + (j+1) = (k+j)+1 by ring, Nat.factorial_succ]
    push_cast; ring

/-- `𝖯^m_k 𝖰^m_j → (k+m)!/((k-m)! 2m)` as `x → 1⁻`, for `1 ≤ m ≤ k`. -/
theorem legPI_tendsto_PQ_one {k j m : ℕ} (hm : 0 < m) (hk : m ≤ k) :
    Tendsto (fun x : ℝ => ferrersP k m x * ferrersQ j m x) (𝓝[<] (1:ℝ))
      (𝓝 (((k+m).factorial : ℂ) / ((k-m).factorial * (2*m)))) := by
  have hp : poch ((k:ℂ)-m+1) (2*m) ≠ 0 := by
    have := legPI_poch_nat (k-m) (2*m)
    rw [show ((k-m:ℕ):ℂ) = (k:ℂ) - m by push_cast [hk]; ring] at this
    intro h; rw [h, zero_mul] at this
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) this.symm
  have h1 := legendre_singular_2 (k:ℂ) m hm hp
  have hreg : LegendreQRegular (j:ℂ) (m:ℂ) := fun n hn => by
    have := congrArg Complex.re hn; simp at this
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg j : (0:ℝ) ≤ j),
      (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hμ : 0 < ((m:ℂ)).re := by simp; exact_mod_cast hm
  have hh : ∀ n : ℕ, (m:ℂ) ≠ n+1/2 := fun n hn => by
    have := congrArg Complex.re hn; simp at this
    have h2 : (2:ℝ)*m = 2*n+1 := by linarith
    have h3 : (2*m : ℕ) = 2*n+1 := by exact_mod_cast h2
    omega
  have h2 := legendre_singular_4 (j:ℂ) (m:ℂ) hreg hμ hh
  have h3 := h1.mul h2
  set c : ℂ := (-1)^m*poch ((k:ℂ)-m+1) (2*m)/(m.factorial:ℂ) * (1/2*cos ((m:ℂ)*π)*Gamma m)
    with hc
  have h4 : (fun x : ℝ => (-1)^m*poch ((k:ℂ)-m+1) (2*m)/(m.factorial:ℂ)*((1-x)/2:ℂ)^((m:ℂ)/2) *
      (1/2*cos ((m:ℂ)*π)*Gamma m*(2/(1-x):ℂ)^((m:ℂ)/2))) =ᶠ[𝓝[<] (1:ℝ)] (fun _ => c) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    have h1x : (0:ℝ) < 1 - x := by linarith
    have e : ((1-x)/2:ℂ)^((m:ℂ)/2) * (2/(1-x):ℂ)^((m:ℂ)/2) = 1 := by
      rw [show ((1-x)/2:ℂ) = (((1-x)/2:ℝ):ℂ) by push_cast; ring,
        show (2/(1-x):ℂ) = ((2/(1-x):ℝ):ℂ) by push_cast; ring,
        ← mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← ofReal_mul,
        show (1-x)/2*(2/(1-x)) = 1 by field_simp]
      simp
    rw [hc]
    linear_combination ((-1)^m*poch ((k:ℂ)-m+1) (2*m)/(m.factorial:ℂ) *
      (1/2*cos ((m:ℂ)*π)*Gamma m)) * e
  have h5 := (h3.congr_right h4).symm.tendsto_nhds (tendsto_const_nhds (x := c))
  convert h5 using 2
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩
  have hpn := legPI_poch_nat (k-(m'+1)) (2*(m'+1))
  rw [show ((k-(m'+1):ℕ):ℂ) = (k:ℂ) - ((m'+1:ℕ):ℂ) by push_cast [hk]; ring,
    show k-(m'+1)+2*(m'+1) = k+(m'+1) by omega] at hpn
  have hcos : cos (((m'+1:ℕ):ℂ)*π) = (-1)^(m'+1) := by
    rw [show (((m'+1:ℕ):ℂ)*π) = ((((m'+1:ℕ):ℝ)*π : ℝ):ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  have hG : Gamma ((m'+1:ℕ):ℂ) = (m'.factorial : ℂ) := by
    rw [show ((m'+1:ℕ):ℂ) = (m':ℂ)+1 by push_cast; ring, Complex.Gamma_nat_eq_factorial]
  have hsq : ((-1:ℂ)^(m'+1))^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hf0 : ((k-(m'+1)).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm0 : ((m':ℂ)+1) ≠ 0 := by norm_cast
  have hmf : (m'.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hc, hcos, hG, ← hpn, Nat.factorial_succ]
  push_cast
  field_simp
  linear_combination (-poch ((k:ℂ)-((m':ℂ)+1)+1) (2*(m'+1))) * hsq


/-- `𝖯^m_k 𝖰^m_j → (-1)^{k+j+1} (k+m)!/((k-m)! 2m)` as `x → -1⁺`, for `1 ≤ m ≤ k`. -/
theorem legPI_tendsto_PQ_neg_one {k j m : ℕ} (hm : 0 < m) (hk : m ≤ k) :
    Tendsto (fun x : ℝ => ferrersP k m x * ferrersQ j m x) (𝓝[>] (-1:ℝ))
      (𝓝 ((-1)^(k+j+1) * (((k+m).factorial : ℂ) / ((k-m).factorial * (2*m))))) := by
  have h := ((legPI_tendsto_PQ_one (j := j) hm hk).comp legPI_tendsto_neg_left).const_mul
    ((-1:ℂ)^(k+j+1))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hP := ferrersP_neg_of_add_eq_nat (ν := (k:ℂ)) (μ := (m:ℂ)) (N := k+m) (by push_cast; ring) hx'
  have hQ := ferrersQ_neg_of_add_eq_nat (ν := (j:ℂ)) (μ := (m:ℂ)) (N := j+m) (by push_cast; ring) (-x)
  rw [neg_neg] at hP hQ
  simp only [Function.comp_apply]
  rw [hP, hQ]
  have : ((-1:ℂ)^(k+m) * (-1)^(j+m+1)) = (-1)^(k+j+1) := by
    rw [← pow_add, show k+m+(j+m+1) = (k+j+1) + 2*m by ring, pow_add, pow_mul]; norm_num
  linear_combination -(ferrersP (k:ℂ) (m:ℂ) (-x) * ferrersQ (j:ℂ) (m:ℂ) (-x)) * this

/-- A function continuous on `(-1,1)` with finite limits at both ends is integrable on `[-1,1]`. -/
theorem legPI_intervalIntegrable_of_tendsto {h : ℝ → ℂ} (hc : ContinuousOn h (Ioo (-1) 1)) {a b : ℂ}
    (ha : Tendsto h (𝓝[>] (-1:ℝ)) (𝓝 a)) (hb : Tendsto h (𝓝[<] (1:ℝ)) (𝓝 b)) :
    IntervalIntegrable h volume (-1) 1 := by
  obtain ⟨M, hM⟩ := legPI_bound hc ((ha.isBigO_one ℝ).trans legPI_one_isBigO_left)
    ((hb.isBigO_one ℝ).trans legPI_one_isBigO_right)
  have h1 : ∀ x ∈ Ioo (-1:ℝ) 1, ‖(fun _ : ℝ => (1:ℂ)) x‖ ≤ 1 * legPIw x := fun x hx => by
    simp only [norm_one, one_mul]; exact legPIw_one_le hx
  have := legPI_intervalIntegrable_mul hc continuousOn_const hM h1
  simpa using this

/-- DLMF 14.17.16 for positive order. -/
theorem legPI_PQ_nat_pos (l m n : ℕ) (hm : 0 < m) (h : l ≠ n) (hl : m ≤ l) :
    (∫ x : ℝ in -1..1, ferrersP l m x*ferrersQ n m x) =
      (1-(-1)^(l+n))*((l+m).factorial:ℂ)/(((l:ℂ)-n)*(l+n+1:ℂ)*(l-m).factorial) := by
  have hreg : ∀ j : ℕ, LegendreQRegular (j:ℂ) (m:ℂ) := fun j n hn => by
    have := congrArg Complex.re hn; simp at this
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg j : (0:ℝ) ≤ j),
      (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  set c : ℕ → ℂ := fun k => ((k+m).factorial : ℂ) / ((k-m).factorial * (2*m)) with hcdef
  set B : ℝ → ℂ := fun x => (m-n-1:ℂ)*(ferrersP l m x * ferrersQ (n+1:ℕ) m x) +
    (n+1:ℂ)*x*(ferrersP l m x * ferrersQ n m x) -
    (m-l-1:ℂ)*(ferrersP (l+1:ℕ) m x * ferrersQ n m x) -
    (l+1:ℂ)*x*(ferrersP l m x * ferrersQ n m x) with hB
  have hBeq : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*(ferrersP l m x*deriv (ferrersQ n m) x -
      ferrersQ n m x*deriv (ferrersP l m) x) = B x := by
    intro x hx
    have r1 := ferrersP_recurrence_4 (l:ℂ) (m:ℂ) hx
    have r2 := ferrersQ_recurrence_4 (n:ℂ) (m:ℂ) (hreg n) hx
    simp only [hB]
    push_cast
    linear_combination ferrersP (l:ℂ) (m:ℂ) x * r2 - ferrersQ (n:ℂ) (m:ℂ) x * r1
  have hx1 : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[<] (1:ℝ)) (𝓝 1) := by
    have := (continuous_ofReal.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1:ℝ)))
    simpa using this
  have hxm : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (-1:ℝ)) (𝓝 (-1)) := by
    have := (continuous_ofReal.tendsto (-1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (-1:ℝ)))
    simpa using this
  have hl1 : m ≤ l+1 := by omega
  have p1 := legPI_tendsto_PQ_one (j := n+1) hm hl
  have p2 := legPI_tendsto_PQ_one (j := n) hm hl
  have p3 := legPI_tendsto_PQ_one (j := n) hm hl1
  have q1 := legPI_tendsto_PQ_neg_one (j := n+1) hm hl
  have q2 := legPI_tendsto_PQ_neg_one (j := n) hm hl
  have q3 := legPI_tendsto_PQ_neg_one (j := n) hm hl1
  have hp := ((((tendsto_const_nhds (x := (m-n-1:ℂ))).mul p1).add
    (((tendsto_const_nhds (x := (n+1:ℂ))).mul hx1).mul p2)).sub
    ((tendsto_const_nhds (x := (m-l-1:ℂ))).mul p3)).sub
    (((tendsto_const_nhds (x := (l+1:ℂ))).mul hx1).mul p2)
  have hq := ((((tendsto_const_nhds (x := (m-n-1:ℂ))).mul q1).add
    (((tendsto_const_nhds (x := (n+1:ℂ))).mul hxm).mul q2)).sub
    ((tendsto_const_nhds (x := (m-l-1:ℂ))).mul q3)).sub
    (((tendsto_const_nhds (x := (l+1:ℂ))).mul hxm).mul q2)
  have hcont : ContinuousOn (fun x => ferrersP l m x * ferrersQ n m x) (Ioo (-1) 1) :=
    (legPI_continuousOn_of_solution' (legPI_ferrersP_isFerrersSolution_mu _ _)).mul
      (legPI_continuousOn_of_solution' (legPI_ferrersQ_isFerrersSolution_mu _ _))
  have hint := legPI_intervalIntegrable_of_tendsto hcont q2 p2
  have hc : (l:ℂ)*(l+1) - n*(n+1) ≠ 0 := by
    rw [show (l:ℂ)*(l+1) - n*(n+1) = ((l:ℂ)-n)*(l+n+1) by ring]
    refine mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast h)) ?_
    exact_mod_cast (Nat.succ_ne_zero (l+n))
  rw [legPI_integral_green_B (legPI_ferrersP_isFerrersSolution_mu _ _)
    (legPI_ferrersQ_isFerrersSolution_mu _ _) hBeq hint hq hp hc]
  have e1 : ((-1:ℂ))^(l+(n+1)+1) = (-1)^(l+n) := by
    rw [show l+(n+1)+1 = (l+n)+2 by ring, pow_add]; norm_num
  have e2 : (-1:ℂ)^(l+n+1) = -(-1)^(l+n) := by rw [pow_succ]; ring
  have e3 : (-1:ℂ)^(l+1+n+1) = (-1)^(l+n) := by
    rw [show l+1+n+1 = (l+n)+2 by ring, pow_add]; norm_num
  have f1 : (l+1+m).factorial = (l+m+1) * (l+m).factorial := by
    rw [show l+1+m = (l+m)+1 by ring, Nat.factorial_succ]
  have f2 : (l+1-m).factorial = (l-m+1) * (l-m).factorial := by
    rw [show l+1-m = (l-m)+1 by omega, Nat.factorial_succ]
  have hlm : ((l-m:ℕ):ℂ) = (l:ℂ) - m := by push_cast [hl]; ring
  have hlm1 : ((l-m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hd1 : ((l:ℂ) - m + 1) ≠ 0 := by
    rw [← hlm]; exact_mod_cast Nat.succ_ne_zero (l-m)
  have hd2 : (l:ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  have hd3 : (l:ℂ) + n + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l+n)
  rw [e1, e2, e3, f1, f2]
  push_cast
  rw [hlm]
  field_simp
  ring

/-- ferrersPQ nat integral. -/
@[dlmf 14.17.E16]
theorem ferrersPQ_nat_integral (l m n : ℕ) (h : l ≠ n) (hl : m ≤ l) :
    (∫ x : ℝ in -1..1, ferrersP l m x*ferrersQ n m x)=(1-(-1)^(l+n))*((l+m).factorial:ℂ)/(((l:ℂ)-n)*(l+n+1:ℂ)*(l-m).factorial) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hreg : LegendreQRegular (n:ℂ) 0 := fun j hj => by
      have := congrArg Complex.re hj; simp at this
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    have hd2 : (l:ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hd3 : (l:ℂ) + n + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l+n)
    have hc : (l:ℂ)*(l+1) - n*(n+1) ≠ 0 := by
      rw [show (l:ℂ)*(l+1) - n*(n+1) = (l-n)*(l+n+1) by ring]; exact mul_ne_zero hd2 hd3
    have hG : (Gamma (-(l:ℂ)))⁻¹ = 0 := by
      rw [inv_eq_zero]; exact Complex.Gamma_neg_nat_eq_zero l
    have hK : legPIK (l:ℂ) = 0 := by unfold legPIK legBdK; rw [hG, mul_zero]
    have hC : legPIC (l:ℂ) = (-1)^l := by
      unfold legPIC; rw [legPI_K'_eq_all, hG]; unfold legBdK; rw [hG]
      simp only [mul_zero, add_zero, sub_zero]
      rw [mul_comm, show ((l:ℂ)*π) = ((l*π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
        Real.cos_nat_mul_pi]; push_cast; ring
    have hcos : cos ((n:ℂ)*π) = (-1)^n := by
      rw [show ((n:ℂ)*π) = ((n*π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
        Real.cos_nat_mul_pi]; push_cast; ring
    have e := legPI_integral_PQ (ν := (l:ℂ)) hreg hc
    simp only [Nat.cast_zero] at e ⊢
    rw [e, hK, hC, hcos]
    simp only [add_zero, Nat.sub_zero]
    have hlf : ((l.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [pow_add]
    field_simp
    ring
  · exact legPI_PQ_nat_pos l m n hm h hl

/-- ferrers triple integral. -/
@[dlmf 14.17.E17]
theorem ferrers_triple_integral (l m n : ℕ) (hl : 0 < l) (hm : 0 < m) (hn : 0 < n) (htri : (|((m:ℤ)-n)| < l ∧ l < m+n) ∨ Even (l+m+n)) :
    (∫ θ : ℝ in 0..π, ferrersQ l 0 (Real.cos θ)*ferrersP m 0 (Real.cos θ)*ferrersP n 0 (Real.cos θ)*Real.sin θ)=0 := by
  sorry

/-! ### Green's identity on `(1, ∞)`

Integrals of products of order-zero Legendre functions over `(1,∞)` (DLMF 14.17.18–20) are
obtained from Green's identity, the boundary variable `x = 1 + 2τ` at `1⁺` with the
logarithmic expansions DLMF 14.8.9 (`legBd_olverQ_log_isBigO`), and the power bounds
DLMF 14.8.12, 14.8.15 at `∞`. Helper names carry the prefix `legExt_`. -/
/-- Complex Green identity for two order-zero Legendre solutions on an open set. -/
theorem legExt_green {ν lam : ℂ} {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (ef : ∀ z ∈ U, (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-0^2/(1-z^2))*f z=0)
    (eg : ∀ z ∈ U, (1-z^2)*iteratedDeriv 2 g z-2*z*deriv g z+(lam*(lam+1)-0^2/(1-z^2))*g z=0)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w : ℂ => (1-w^2)*(f w*deriv g w-g w*deriv f w))
      ((ν*(ν+1) - lam*(lam+1)) * (f z * g z)) z := by
  have hfz := (hf z hz).differentiableAt (hU.mem_nhds hz)
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hf2 := ((hf.deriv hU) z hz).differentiableAt (hU.mem_nhds hz)
  have hg2 := ((hg.deriv hU) z hz).differentiableAt (hU.mem_nhds hz)
  have e1 := ef z hz
  have e2 := eg z hz
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at e1 e2
  rw [iteratedDeriv_succ, iteratedDeriv_one] at e1 e2
  have hsq : HasDerivAt (fun w : ℂ => 1-w^2) (-(2*z)) z := by
    simpa using ((hasDerivAt_id z).pow 2).const_sub 1
  refine (hsq.mul ((hfz.hasDerivAt.mul hg2.hasDerivAt).sub
    (hgz.hasDerivAt.mul hf2.hasDerivAt))).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  linear_combination (f z)*e2-(g z)*e1

/-- The domain `{z | z - 1 ∈ slitPlane}` of the Legendre functions `P_ν, 𝑸_ν`. -/
def legExtU : Set ℂ := {z : ℂ | z-1 ∈ slitPlane}

theorem legExt_isOpen_U : IsOpen legExtU := isOpen_sub_one_mem_slitPlane

theorem legExt_mem_U {x : ℝ} (hx : 1 < x) : (x:ℂ) ∈ legExtU := by
  show (x:ℂ) - 1 ∈ slitPlane
  exact Or.inl (by simp; linarith)

/-- Green's identity on `(1,∞)`: the improper integral of `f g` is given by the limits of the
boundary form `(λ+1) f (x g - g₁) - (ν+1) g (x f - f₁)` at `1⁺` and at `∞`. -/
theorem legExt_integral_green {f g f1 g1 : ℂ → ℂ} {ν lam B1 : ℂ}
    (hf : DifferentiableOn ℂ f legExtU) (hg : DifferentiableOn ℂ g legExtU)
    (ef : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-0^2/(1-z^2))*f z=0)
    (eg : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 g z-2*z*deriv g z+(lam*(lam+1)-0^2/(1-z^2))*g z=0)
    (hrf : ∀ x : ℝ, 1 < x → (1-(x:ℂ)^2)*deriv f x = (ν+1)*(x*f x - f1 x))
    (hrg : ∀ x : ℝ, 1 < x → (1-(x:ℂ)^2)*deriv g x = (lam+1)*(x*g x - g1 x))
    (hint : ∀ R : ℝ, 1 < R → IntervalIntegrable (fun x : ℝ => f x * g x) volume 1 R)
    (h1 : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      (𝓝[>] 1) (𝓝 B1))
    (hinf : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      atTop (𝓝 0))
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    HasIntegralAtTop (fun x : ℝ => f x * g x) 1 (-B1/(ν*(ν+1) - lam*(lam+1))) := by
  set c := ν*(ν+1) - lam*(lam+1) with hcdef
  set B : ℝ → ℂ := fun x => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x) with hB
  set W : ℝ → ℂ := fun y => (fun w : ℂ => (1-w^2)*(f w*deriv g w-g w*deriv f w)) (y:ℂ) with hW
  have hd : ∀ y : ℝ, 1 < y → HasDerivAt W (c * (f y * g y)) y := fun y hy =>
    (legExt_green legExt_isOpen_U hf hg ef eg (legExt_mem_U hy)).comp_ofReal
  have hWB : ∀ y : ℝ, 1 < y → W y = B y := by
    intro y hy
    simp only [hW, hB]
    linear_combination (f y) * hrg y hy - (g y) * hrf y hy
  have hI : ∀ R : ℝ, 1 < R → (∫ x in (1:ℝ)..R, f x * g x) = (B R - B1) / c := by
    intro R hR
    have ha : Tendsto W (𝓝[>] 1) (𝓝 B1) := h1.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y (hy : 1 < y) using (hWB y hy).symm)
    have hb : Tendsto W (𝓝[<] R) (𝓝 (W R)) :=
      (hd R hR).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have e := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR
      (fun y hy => hd y hy.1) ((hint R hR).const_mul c) ha hb
    rw [intervalIntegral.integral_const_mul, hWB R hR] at e
    rw [eq_div_iff hc, mul_comm, e]
  have hlim : Tendsto (fun R : ℝ => (B R - B1) / c) atTop (𝓝 ((0 - B1)/c)) :=
    (hinf.sub tendsto_const_nhds).div_const c
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR using (hI R hR).symm


/-- A function continuous on `(1,∞)` and `O(((x-1)/2)^{-1/2})` at `1⁺` is integrable on every
`[1,R]`. -/
theorem legExt_intervalIntegrable {h : ℝ → ℂ} (hc : ContinuousOn h (Ioi 1))
    (hO : h =O[𝓝[>] (1:ℝ)] (fun x : ℝ => ((x-1)/2)^(-(1/2:ℝ)))) {R : ℝ} (hR : 1 < R) :
    IntervalIntegrable h volume 1 R := by
  have hw : IntervalIntegrable (fun x : ℝ => (x-1)^(-(1/2:ℝ))) volume 1 2 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1/2:ℝ)) (by norm_num)
      (a := 0) (b := 1)).comp_sub_right 1
    norm_num at this ⊢; exact this
  have hO' : h =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)^(-(1/2:ℝ))) := by
    refine hO.trans (Asymptotics.IsBigO.of_bound ((2:ℝ)^(1/2:ℝ)) ?_)
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    have h0 : 0 ≤ x - 1 := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg h0 _), Real.div_rpow h0 (by norm_num),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have hmeas : StronglyMeasurableAtFilter h (𝓝[>] (1:ℝ)) volume :=
    hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 1
  have hwI : IntegrableAtFilter (fun x : ℝ => (x-1)^(-(1/2:ℝ))) (𝓝[>] (1:ℝ)) volume := by
    refine ⟨Ioo 1 2, Ioo_mem_nhdsGT (by norm_num), ?_⟩
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1:ℝ) ≤ 2)).1 hw
    exact this
  obtain ⟨s, hs, hsI⟩ := hO'.integrableAtFilter hmeas hwI
  obtain ⟨u, hu, hU⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hs
  simp only [mem_Ioi] at hu
  set b := min ((1+u)/2) ((1+R)/2) with hb
  have hb1 : 1 < b := lt_min (by linarith) (by linarith)
  have hbu : b < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hbR : b < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 : IntervalIntegrable h volume 1 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb1.le]
    exact hsI.mono_set (fun y hy => hU ⟨hy.1, lt_of_le_of_lt hy.2 hbu⟩)
  have h2 : IntervalIntegrable h volume b R := by
    refine (hc.mono ?_).intervalIntegrable
    intro y hy
    rw [uIcc_of_le hbR.le] at hy
    exact lt_of_lt_of_le hb1 hy.1
  exact h1.trans h2

/-- An expansion `f = -k ln τ + c + O(τ ln τ)` with `τ = (x-1)/2` gives `f = O(τ^{-1/4})`. -/
theorem legExt_isBigO_weight {f : ℝ → ℂ} {k c : ℂ}
    (hf : (fun x => f x + k * Real.log ((x-1)/2) - c) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2))) :
    f =O[𝓝[>] (1:ℝ)] (fun x : ℝ => ((x-1)/2)^(-(1/4:ℝ))) := by
  have hτ : Tendsto (fun x : ℝ => (x-1)/2) (𝓝[>] (1:ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun x : ℝ => (x-1)/2) (𝓝 1) (𝓝 ((1-1)/2)) :=
        (tendsto_id.sub tendsto_const_nhds).div_const 2
      simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
      simp only [mem_Ioi]; linarith
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (1:ℝ), 0 < (x-1)/2 ∧ (x-1)/2 ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 3 by norm_num)] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hone : (fun _ : ℝ => (1:ℝ)) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => ((x-1)/2)^(-(1/4:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hev] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hx.1 _)]
    exact legPI_rpow_ge_one hx.1 hx.2
  have hlog : (fun x : ℝ => Real.log ((x-1)/2)) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => ((x-1)/2)^(-(1/4:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 4 ?_
    filter_upwards [hev] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx.1 _)]
    exact legPI_abs_log_le hx.1 hx.2
  have htl : Tendsto (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2)) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).comp (hτ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  have h1 := (hf.trans (htl.isBigO_one ℝ)).trans hone
  have h2 := (isBigO_ofReal_left.mpr hlog).const_mul_left k
  have h3 := (isBigO_const_one ℝ c (𝓝[>] (1:ℝ))).trans hone
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- Product of two functions with logarithmic expansions at `1⁺` is integrable on `[1,R]`. -/
theorem legExt_intervalIntegrable_mul {f g : ℝ → ℂ} {kf cf kg cg : ℂ}
    (hfc : ContinuousOn f (Ioi 1)) (hgc : ContinuousOn g (Ioi 1))
    (hf : (fun x => f x + kf * Real.log ((x-1)/2) - cf) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2)))
    (hg : (fun x => g x + kg * Real.log ((x-1)/2) - cg) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2))) {R : ℝ} (hR : 1 < R) :
    IntervalIntegrable (fun x => f x * g x) volume 1 R := by
  refine legExt_intervalIntegrable (hfc.mul hgc) (((legExt_isBigO_weight hf).mul
    (legExt_isBigO_weight hg)).congr' (EventuallyEq.refl _ _) ?_) hR
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  rw [← Real.rpow_add (by linarith)]; norm_num


/-- The polynomial remainder in the boundary form at `1⁺` (`x = 1 + 2τ`). -/
def legExtR (kf kg cf cg rf rg n l : ℂ) (v : Fin 11 → ℂ) : ℂ :=
  (2*kf*kg*l - 2*kf*kg*n)*v 2 +
    (-2*kg*l + 2*kg*n)*v 7*v 0 +
    (-2*kf*l + 2*kf*n)*v 8*v 0 +
    (-2*cf*kg*l + 2*cf*kg*n - 2*cg*kf*l + 2*cg*kf*n)*v 1 +
    (2*l - 2*n)*v 3*v 4*v 0 +
    (2*cg*l - 2*cg*n)*v 3*v 0 +
    (2*cf*l - 2*cf*n)*v 4*v 0 +
    (2*cf*cg*l - 2*cf*cg*n)*v 0 +
    (kg*n + kg)*v 7 +
    (-kf*l - kf)*v 8 +
    (kf*l + kf)*v 9 +
    (-kg*n - kg)*v 10 +
    (l - n)*v 3*v 4 +
    (-l - 1)*v 3*v 5 +
    (-cg*n - cg - l*rg - rg)*v 3 +
    (n + 1)*v 4*v 6 +
    (cf*l + cf + n*rf + rf)*v 4 +
    (-cf*l - cf)*v 5 +
    (cg*n + cg)*v 6

theorem legExt_continuous_R (kf kg cf cg rf rg n l : ℂ) : Continuous (legExtR kf kg cf cg rf rg n l) := by
  unfold legExtR; fun_prop

/-- Limit of the Green boundary form at an endpoint `x = 1 + 2τ`, `τ → 0⁺`, for expansions
`f = -k_f ln τ + c_f + O(τ ln τ)` with `k_{f₁} = k_f`, `c_{f₁} = c_f + r_f`, `(ν+1) r_f = -2 k_f`. -/
theorem legExt_bdry {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (hx : ∀ᶠ x : ℝ in l, (x:ℂ) = 1 + 2*τ x) {f g g1 f1 : ℝ → ℂ} {ν lam kf kg cf cg rf rg : ℂ}
    (hf : (fun x => f x + kf * Real.log (τ x) - cf) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg : (fun x => g x + kg * Real.log (τ x) - cg) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg1 : (fun x => g1 x + kg * Real.log (τ x) - (cg + rg)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hf1 : (fun x => f1 x + kf * Real.log (τ x) - (cf + rf)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hrg : (lam+1)*rg = -2*kg) (hrf : (ν+1)*rf = -2*kf) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) l
      (𝓝 (2*(kg*cf - kf*cg))) := by
  obtain ⟨cT, cTU, cTUU, -, -⟩ := legPI_basic_limits hτ
  obtain ⟨c1, d1⟩ := legPI_err_limits hτ hf
  obtain ⟨c2, d2⟩ := legPI_err_limits hτ hg
  obtain ⟨c3, d3⟩ := legPI_err_limits hτ hg1
  obtain ⟨c4, d4⟩ := legPI_err_limits hτ hf1
  set U : ℝ → ℂ := fun x => ((Real.log (τ x) : ℝ) : ℂ) with hU
  set V : ℝ → Fin 11 → ℂ := fun x => ![(τ x : ℂ), (τ x : ℂ) * U x, (τ x : ℂ) * U x * U x,
    f x + kf * U x - cf, g x + kg * U x - cg, g1 x + kg * U x - (cg + rg),
    f1 x + kf * U x - (cf + rf), U x * (f x + kf * U x - cf), U x * (g x + kg * U x - cg),
    U x * (g1 x + kg * U x - (cg + rg)), U x * (f1 x + kf * U x - (cf + rf))] with hV
  have cV : Tendsto V l (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · exact cT
    · exact cTU
    · exact cTUU
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have cR := ((legExt_continuous_R kf kg cf cg rf rg ν lam).tendsto 0).comp cV
  have hR0 : legExtR kf kg cf cg rf rg ν lam 0 = 0 := by simp [legExtR]
  rw [hR0] at cR
  have key := (tendsto_const_nhds (x := 2*(kg*cf - kf*cg))).add cR
  rw [add_zero] at key
  refine key.congr' ?_
  filter_upwards [hx] with x hx
  simp only [Function.comp_apply, hV, legExtR, Matrix.cons_val, hU]
  rw [hx]
  linear_combination (cf - kf*U x) * hrg - (cg - kg*U x) * hrf


theorem legExt_tendsto_half :
    Tendsto (fun x : ℝ => (x-1)/2) (𝓝[>] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => (x-1)/2) (𝓝 1) (𝓝 ((1-1)/2)) :=
      (tendsto_id.sub tendsto_const_nhds).div_const 2
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    simp only [mem_Ioi]; linarith

theorem legExt_hx : ∀ᶠ x : ℝ in 𝓝[>] (1:ℝ), (x:ℂ) = 1 + 2*(((x-1)/2 : ℝ) : ℂ) :=
  Eventually.of_forall fun x => by push_cast; ring

/-- `(x-1) ln(x-1) = O(τ ln τ)` with `τ = (x-1)/2`, as `x → 1⁺`. -/
theorem legExt_sub_one_log_isBigO :
    (fun x : ℝ => (x-1)*Real.log (x-1)) =O[𝓝[>] (1:ℝ)] (fun x => (x-1)/2 * Real.log ((x-1)/2)) := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 2 by norm_num)] with x hx
  have ht0 : 0 < (x-1)/2 := by linarith [hx.1]
  have ht1 : (x-1)/2 ≤ 1/2 := by linarith [hx.2]
  have hl2 : Real.log 2 ≤ |Real.log ((x-1)/2)| := by
    rw [abs_of_nonpos (Real.log_nonpos ht0.le (by linarith)), ← Real.log_inv]
    exact Real.log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) ht0]; linarith)
  have hL : (x-1)*Real.log (x-1) = 2*((x-1)/2)*(Real.log 2 + Real.log ((x-1)/2)) := by
    rw [← Real.log_mul (by norm_num) ht0.ne']; ring_nf
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hL, abs_mul, abs_mul, abs_mul, abs_of_pos ht0, abs_two]
  have h2 : |Real.log 2 + Real.log ((x-1)/2)| ≤ 2 * |Real.log ((x-1)/2)| := by
    calc _ ≤ |Real.log 2| + |Real.log ((x-1)/2)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos (Real.log_pos (by norm_num))]; linarith
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2*((x-1)/2))
  linarith

/-- `P_α(z) = 𝐅(α+1,-α;1;(1-z)/2)` for every `z`. -/
theorem legExt_associatedP_eq (α z : ℂ) :
    associatedP α 0 z = regularizedGaussHG (α+1) (-α) 1 ((1-z)/2) := by
  simp [associatedP]

/-- `P_α - 1 = O(τ ln τ)` with `τ = (x-1)/2`, as `x → 1⁺`. -/
theorem legExt_P_isBigO (α : ℂ) :
    (fun x : ℝ => associatedP α 0 x + (0:ℂ) * Real.log ((x-1)/2) - 1) =O[𝓝[>] (1:ℝ)]
      (fun x => (x-1)/2 * Real.log ((x-1)/2)) := by
  have hfun : (fun y : ℝ => associatedP α 0 y) =
      fun y : ℝ => regularizedGaussHG (α+1) (-α) 1 ((1-(y:ℂ))/2) :=
    funext fun y => legExt_associatedP_eq α y
  have hw : ((1-((1:ℝ):ℂ))/2) ∈ cutPlane := by simpa using zero_mem_cutPlane
  have hd : DifferentiableAt ℝ (fun y : ℝ => associatedP α 0 y) 1 := by
    rw [hfun]
    exact ((differentiableAt_regularizedGaussHG _ _ _ hw).restrictScalars ℝ).comp (1:ℝ)
      (by fun_prop)
  have h1 := hd.isBigO_sub.mono (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
  have hv : associatedP α 0 ((1:ℝ):ℂ) = 1 := by
    rw [legExt_associatedP_eq]; simp [regularizedGaussHG_at_zero]
  simp only [hv] at h1
  have h2 : (fun x : ℝ => x - 1) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (((x-1)/2 : ℝ) : ℂ)) := by
    refine Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_two]
    linarith [abs_nonneg (x-1)]
  have h3 := legBd_isBigO_self_mul_log.comp_tendsto legExt_tendsto_half
  refine (h1.trans (h2.trans h3)).congr_left fun x => ?_
  ring

/-- DLMF 14.8.9 in the variable `τ = (x-1)/2`: `Q_α + ½ ln τ - (-γ - ψ(α+1)) = O(τ ln τ)`. -/
theorem legExt_Q_isBigO {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => associatedQ α 0 x + (1/2:ℂ) * Real.log ((x-1)/2) - legPIcpos α)
      =O[𝓝[>] (1:ℝ)] (fun x => (x-1)/2 * Real.log ((x-1)/2)) := by
  have hp := legPI_regular_arg h
  have hG : Gamma (α+1) ≠ 0 := Gamma_ne_zero hp
  refine (((legBd_olverQ_log_isBigO α).const_mul_left (Gamma (α+1))).trans
    legExt_sub_one_log_isBigO).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  have h1 : (0:ℝ) < x - 1 := by linarith
  have hl : log ((x:ℂ)-1) = ((Real.log (x-1) : ℝ) : ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; rfl, ofReal_log h1.le]
  have hl2 : Real.log ((x-1)/2) = Real.log (x-1) - Real.log 2 :=
    Real.log_div h1.ne' (by norm_num)
  have h2 : log (2:ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  rw [DLMF.Gamma.recipGammaDeriv_one_eq hp, hl, hl2, h2]
  simp only [associatedQ, zero_mul, Complex.exp_zero, one_mul, legPIcpos]
  push_cast
  field_simp
  ring_nf

/-- Expansion of `P_{α+1}` at `1⁺` in the shape required by `legExt_bdry`. -/
theorem legExt_P_isBigO_succ (α : ℂ) :
    (fun x : ℝ => associatedP (α+1) 0 x + (0:ℂ) * Real.log ((x-1)/2) - (1 + 0)) =O[𝓝[>] (1:ℝ)]
      (fun x => (x-1)/2 * Real.log ((x-1)/2)) :=
  (legExt_P_isBigO (α+1)).congr_left fun x => by ring

/-- Expansion of `Q_{α+1}` at `1⁺` in the shape required by `legExt_bdry`. -/
theorem legExt_Q_isBigO_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => associatedQ (α+1) 0 x + (1/2:ℂ) * Real.log ((x-1)/2) -
      (legPIcpos α + (legPIcpos (α+1) - legPIcpos α))) =O[𝓝[>] (1:ℝ)]
      (fun x => (x-1)/2 * Real.log ((x-1)/2)) :=
  (legExt_Q_isBigO (legPI_regular_succ h)).congr_left fun x => by ring


/-- `𝑸_ν(x) = O(x^{-Re ν - 1})` as `x → ∞`, for every degree `ν`. -/
theorem legExt_olverQ_isBigO_atTop (ν : ℂ) :
    (fun x : ℝ => olverQ ν 0 x) =O[atTop] (fun x : ℝ => x^(-(ν.re+1))) := by
  set G := regularizedGaussHG ((ν+0+2)/2) ((ν+0+1)/2) (ν+3/2)
  have hG : Tendsto (fun x : ℝ => G (1/(x:ℂ)^2)) atTop (𝓝 (G 0)) :=
    (analyticAt_regularizedGaussHG _ _ _ zero_mem_cutPlane).continuousAt.tendsto.comp
      tendsto_one_div_sq_atTop
  have hG1 := hG.isBigO_one ℝ
  have hP : (fun x : ℝ => ((x:ℂ)^(ν+1))⁻¹) =O[atTop] (fun x : ℝ => x^(-(ν.re+1))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos hx, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx _), one_mul, Real.rpow_neg hx.le]
    simp
  have := (hP.mul hG1).const_mul_left ((Real.sqrt π : ℂ) / 2^(ν+1))
  refine (this.congr' ?_ (by filter_upwards with x; simp)).trans (isBigO_refl _ _)
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [olverQ, legendreBranchPower, zero_div, zero_mul, Complex.exp_zero, mul_one, add_zero, G]
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hxn : (x:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have h2n : (2:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  field_simp

/-- `P_ν(x) = O(x^{Re ν})` as `x → ∞`, when `Re ν > -1/2`. -/
theorem legExt_associatedP_isBigO_atTop {ν : ℂ} (hν : -1/2 < ν.re) :
    (fun x : ℝ => associatedP ν 0 x) =O[atTop] (fun x : ℝ => x^(ν.re)) := by
  have h1 := (legBd_associatedP_tendsto_atTop hν 0).isBigO_one ℝ
  have hP : (fun x : ℝ => (x:ℂ)^ν) =O[atTop] (fun x : ℝ => x^(ν.re)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_cpow_eq_rpow_re_of_pos hx, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _),
      one_mul]
  refine ((hP.mul h1).congr' ?_ (by filter_upwards with x; simp))
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [← mul_assoc, ← cpow_add _ _ hx0]; simp

/-- The Green boundary form tends to `0` at `∞` under power bounds with `a < b`. -/
theorem legExt_tendsto_zero_atTop {f g f1 g1 : ℝ → ℂ} {ν lam : ℂ} {a b : ℝ} (hab : a < b)
    (hf : f =O[atTop] (fun x : ℝ => x^a)) (hf1 : f1 =O[atTop] (fun x : ℝ => x^(a+1)))
    (hg : g =O[atTop] (fun x : ℝ => x^(-b-1))) (hg1 : g1 =O[atTop] (fun x : ℝ => x^(-b-1))) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) atTop
      (𝓝 0) := by
  have hX : (fun x : ℝ => (x:ℂ)) =O[atTop] (fun x : ℝ => x^(1:ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [abs_of_pos hx]
  have hone : (fun _ : ℝ => (1:ℂ)) =O[atTop] (fun x : ℝ => x^(1:ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp [abs_of_pos (show (0:ℝ) < x by linarith), hx]
  have hT : Tendsto (fun x : ℝ => x^(a-b)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_neg_atTop (y := b - a) (by linarith)
  have hE : ∀ p q : ℝ, p + q = a - b → ∀ u v : ℝ → ℂ, u =O[atTop] (fun x : ℝ => x^p) →
      v =O[atTop] (fun x : ℝ => x^q) → Tendsto (fun x => u x * v x) atTop (𝓝 0) := by
    intro p q hpq u v hu hv
    refine ((hu.mul hv).congr' (EventuallyEq.refl _ _) ?_).trans_tendsto hT
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx, hpq]
  have t1 := hE (a) (1 + (-b-1)) (by ring) f (fun x => (x:ℂ) * g x) hf
    ((hX.mul hg).congr' (EventuallyEq.refl _ _) (by
      filter_upwards [eventually_gt_atTop 0] with x hx; rw [← Real.rpow_add hx]))
  have t2 := hE a (1 + (-b-1)) (by ring) f g1 hf (((hone.mul hg1).congr' (by
      filter_upwards with x; simp) (by
      filter_upwards [eventually_gt_atTop 0] with x hx; rw [← Real.rpow_add hx])))
  have t3 := hE (-b-1) (1 + a) (by ring) g (fun x => (x:ℂ) * f x) hg
    ((hX.mul hf).congr' (EventuallyEq.refl _ _) (by
      filter_upwards [eventually_gt_atTop 0] with x hx; rw [← Real.rpow_add hx]))
  have t4 := hE (-b-1) (a+1) (by ring) g f1 hg hf1
  have := ((t1.sub t2).const_mul (lam+1)).sub ((t3.sub t4).const_mul (ν+1))
  simp only [mul_zero, sub_zero] at this
  refine this.congr fun x => ?_
  ring


/-- `𝑸_ν = Γ(ν+1) 𝑸_ν` at order zero. -/
theorem legExt_associatedQ_eq (α : ℂ) :
    associatedQ α 0 = fun z => Gamma (α+1) * olverQ α 0 z := by
  funext z; simp [associatedQ]

theorem legExt_differentiableOn_P (α : ℂ) : DifferentiableOn ℂ (associatedP α 0) legExtU :=
  (associatedP_analytic α 0).differentiableOn

theorem legExt_differentiableOn_Q (α : ℂ) : DifferentiableOn ℂ (associatedQ α 0) legExtU := by
  rw [legExt_associatedQ_eq]
  exact (olverQ_analytic α 0).differentiableOn.const_mul _

theorem legExt_ode_P (α : ℂ) : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 (associatedP α 0) z -
    2*z*deriv (associatedP α 0) z + (α*(α+1)-0^2/(1-z^2))*associatedP α 0 z = 0 :=
  fun _ hz => associatedP_ode α 0 hz

theorem legExt_ode_Q (α : ℂ) : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 (associatedQ α 0) z -
    2*z*deriv (associatedQ α 0) z + (α*(α+1)-0^2/(1-z^2))*associatedQ α 0 z = 0 := by
  intro z hz
  have e := olverQ_ode α 0 hz
  rw [legExt_associatedQ_eq, iteratedDeriv_const_mul_field, deriv_const_mul_field]
  linear_combination Gamma (α+1) * e

theorem legExt_rec_P (α : ℂ) : ∀ x : ℝ, 1 < x →
    (1-(x:ℂ)^2)*deriv (associatedP α 0) x = (α+1)*(x*associatedP α 0 x - associatedP (α+1) 0 x) :=
  fun x hx => by rw [associatedP_recurrence_4 α 0 (legExt_mem_U hx)]; ring

theorem legExt_rec_Q {α : ℂ} (h : LegendreQRegular α 0) : ∀ x : ℝ, 1 < x →
    (1-(x:ℂ)^2)*deriv (associatedQ α 0) x = (α+1)*(x*associatedQ α 0 x - associatedQ (α+1) 0 x) :=
  fun x hx => by rw [associatedQ_recurrence_4 α 0 h (legExt_mem_U hx)]; ring

theorem legExt_continuousOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f legExtU) :
    ContinuousOn (fun x : ℝ => f x) (Ioi 1) := fun _ hx =>
  ((hf _ (legExt_mem_U hx)).differentiableAt (legExt_isOpen_U.mem_nhds (legExt_mem_U hx))
    ).continuousAt.comp_of_eq continuous_ofReal.continuousAt rfl |>.continuousWithinAt

/-- `Q_ν(x) = O(x^{-Re ν - 1})` as `x → ∞`. -/
theorem legExt_associatedQ_isBigO_atTop (α : ℂ) :
    (fun x : ℝ => associatedQ α 0 x) =O[atTop] (fun x : ℝ => x^(-α.re-1)) := by
  rw [legExt_associatedQ_eq]
  exact ((legExt_olverQ_isBigO_atTop α).const_mul_left _).congr' (EventuallyEq.refl _ _)
    (by filter_upwards with x; ring_nf)

/-- Lowering the exponent of a power bound at `∞`. -/
theorem legExt_isBigO_rpow_mono {f : ℝ → ℂ} {p q : ℝ} (hpq : p ≤ q)
    (h : f =O[atTop] (fun x : ℝ => x^p)) : f =O[atTop] (fun x : ℝ => x^q) := by
  refine h.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hx hpq

/-! ### Uniform bounds on `(1,∞)` and the diagonal integral 14.17.20 -/

/-- `𝑄_λ(x) = Γ(λ+1) √π 2^{-λ-1} x^{-λ-1} 𝐅(λ/2+1, λ/2+1/2; λ+3/2; x^{-2})` for `x > 0`. -/
theorem legPIU_associatedQ_ext (lam : ℂ) {x : ℝ} (hx0 : 0 < x) :
    associatedQ lam 0 x = Gamma (lam+1) * ((Real.sqrt π : ℂ) * ((2:ℂ)^(lam+1))⁻¹ *
      ((x:ℂ)^(lam+1))⁻¹ * regularizedGaussHG ((lam+0+2)/2) ((lam+0+1)/2) (lam+3/2) (1/(x:ℂ)^2)) := by
  simp only [associatedQ, olverQ, legendreBranchPower, zero_div, zero_mul, Complex.exp_zero,
    mul_one, add_zero, one_mul]
  have hx0' : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hxn : (x:ℂ)^(lam+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0')
  have h2n : (2:ℂ)^(lam+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  field_simp

/-- `𝐅(a,b;a+b;y)` is `O((1-y)^{-1/4})` on `[0,1)`, uniformly for `‖a‖, ‖b‖ ≤ R`. -/
theorem legPIU_bound_real (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ∀ y : ℝ, 0 ≤ y →
    y < 1 → ‖regularizedGaussHG a b (a+b) (y:ℂ)‖ ≤ M * (1-y)^(-(1/4:ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := legPIU_bound_zb R
  obtain ⟨MF, hMF⟩ := legPIU_bound_F (2*|R| + 1)
  refine ⟨max MF 0 + C, by positivity, fun a b ha hb y hy0 hy1 => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have hp : 1 ≤ (1-y)^(-(1/4:ℝ)) := legPI_rpow_ge_one (by linarith) (by linarith)
  have hn : ‖(y:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]; exact hy1
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn]
  by_cases hyh : y ≤ 1/2
  · have hn' : ‖(y:ℂ)‖ ≤ 1/2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]; exact hyh
    have hab : ‖a+b‖ ≤ 2*|R|+1 := by
      calc ‖a+b‖ ≤ ‖a‖+‖b‖ := norm_add_le _ _
        _ ≤ 2*|R|+1 := by linarith
    calc _ ≤ MF := hMF _ _ _ _ (by linarith [abs_nonneg R]) (by linarith [abs_nonneg R]) hab hn'
      _ ≤ max MF 0 + C := by linarith [le_max_left MF 0]
      _ ≤ (max MF 0 + C) * (1-y)^(-(1/4:ℝ)) :=
          le_mul_of_one_le_right (by linarith [le_max_right MF 0]) hp
  · push Not at hyh
    have h := hC a b ha hb (1-y) (by linarith) (by linarith)
    rw [show (1:ℂ) - ((1-y:ℝ):ℂ) = (y:ℂ) by push_cast; ring] at h
    have := Real.rpow_nonneg (show (0:ℝ) ≤ 1-y by linarith) (-(1/4:ℝ))
    nlinarith [le_max_right MF 0]

/-- Uniform bound on `(1,∞)`: `‖𝑄_λ(x)‖ ≤ M (x-1)^{-1/4} x^{-(Re ν - r) - 3/4}` for `λ` near a
regular `ν`, with `r ≤ r₀` prescribed. -/
theorem legPIU_bound_Qext {ν : ℂ} (hν : LegendreQRegular ν 0) {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r0 ∧ ∃ M : ℝ, 0 ≤ M ∧
    ∀ lam : ℂ, ‖lam - ν‖ ≤ r → LegendreQRegular lam 0 ∧ ∀ x : ℝ, 1 < x →
      ‖associatedQ lam 0 x‖ ≤ M * ((x-1)^(-(1/4:ℝ)) * x^(-(ν.re-r)-3/4)) := by
  have hν1 := legHyp_nu hν
  have o : IsOpen {lam : ℂ | (Gamma (lam+0+1))⁻¹ ≠ 0} :=
    isOpen_ne_fun (continuous_recip_Gamma.comp (by fun_prop)) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp o ν (by simpa using inv_ne_zero (Gamma_ne_zero hν1))
  set r := min (ε/2) r0
  have hr : 0 < r := lt_min (by positivity) hr0
  set K := Metric.closedBall ν r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hreg : ∀ lam ∈ K, LegendreQRegular lam 0 := fun lam hl => legHyp_regular_of_recip (hball (by
    rw [Metric.mem_ball]; have := Metric.mem_closedBall.mp hl
    have : r ≤ ε/2 := min_le_left _ _; linarith))
  obtain ⟨B1, hB10, hB1⟩ := legPIU_bound_on (f := fun lam : ℂ => Gamma (lam+1)) hK
    (fun lam hl => (ContinuousAt.comp (g := Gamma) (f := fun l : ℂ => l + 1)
      (differentiableAt_Gamma _ (by simpa using legHyp_nu (hreg lam hl))).continuousAt
      (by fun_prop)).continuousWithinAt)
  obtain ⟨B2, hB20, hB2⟩ := legPIU_bound_on (f := fun lam : ℂ => ((2:ℂ)^(lam+1))⁻¹) hK
    ((continuous_const_cpow' two_ne_zero |>.comp (continuous_id.add continuous_const)).inv₀
      (fun lam => cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))).continuousOn
  obtain ⟨MS, hMS0, hMS⟩ := legPIU_bound_real (‖ν‖ + r + 2)
  refine ⟨r, hr, min_le_right _ _, Real.sqrt π * B1 * B2 * MS, by positivity, fun lam hl => ?_⟩
  have hlK : lam ∈ K := Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hl)
  refine ⟨hreg lam hlK, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlam : ‖lam‖ ≤ ‖ν‖ + r := by
    calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
      _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hre : ν.re - r ≤ lam.re := by
    have := Complex.abs_re_le_norm (lam - ν)
    rw [sub_re] at this
    linarith [abs_le.mp (le_trans this hl)]
  have hy0 : (0:ℝ) ≤ 1/x^2 := by positivity
  have hy1 : 1/x^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have hF := hMS ((lam+0+2)/2) ((lam+0+1)/2) ?_ ?_ (1/x^2) hy0 hy1
  rotate_left
  · calc ‖(lam+0+2)/2‖ ≤ ‖lam+0+2‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
      _ ≤ ‖lam‖ + 2 := by simpa using norm_add_le lam 2
      _ ≤ _ := by linarith
  · calc ‖(lam+0+1)/2‖ ≤ ‖lam+0+1‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
      _ ≤ ‖lam‖ + 1 := by simpa using norm_add_le lam 1
      _ ≤ _ := by linarith
  rw [show (lam+0+2)/2 + (lam+0+1)/2 = lam + 3/2 by ring,
    show ((1/x^2 : ℝ) : ℂ) = 1/(x:ℂ)^2 by push_cast; ring] at hF
  have hxp : ‖((x:ℂ)^(lam+1))⁻¹‖ ≤ x^(-(ν.re-r)-1) := by
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos hx0, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by simp; linarith)
  -- `(1 - x^{-2})^{-1/4} x^{-σ-1} ≤ (x-1)^{-1/4} x^{-σ-3/4}`
  have hw : (1-1/x^2)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1) ≤ (x-1)^(-(1/4:ℝ)) * x^(-(ν.re-r)-3/4) := by
    have h1 : (1-1/x^2)^(-(1/4:ℝ)) ≤ ((x-1)/x)^(-(1/4:ℝ)) := by
      refine Real.rpow_le_rpow_of_nonpos (div_pos (by linarith) hx0) ?_ (by norm_num)
      rw [div_le_iff₀ hx0]; field_simp; nlinarith
    have h2 : ((x-1)/x)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1) = (x-1)^(-(1/4:ℝ)) * x^(-(ν.re-r)-3/4) := by
      rw [Real.div_rpow (by linarith) hx0.le, show -(ν.re-r)-3/4 = (1/4:ℝ) + (-(ν.re-r)-1) by ring,
        Real.rpow_add hx0, Real.rpow_neg hx0.le]
      field_simp
    calc _ ≤ ((x-1)/x)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)
      _ = _ := h2
  have e1 := hB1 lam hlK
  have e2 := hB2 lam hlK
  have hsq : ‖(Real.sqrt π : ℂ)‖ = Real.sqrt π := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [legPIU_associatedQ_ext lam hx0, norm_mul, norm_mul, norm_mul, norm_mul, hsq]
  calc ‖Gamma (lam+1)‖ * (Real.sqrt π * ‖((2:ℂ)^(lam+1))⁻¹‖ * ‖((x:ℂ)^(lam+1))⁻¹‖ *
        ‖regularizedGaussHG ((lam+0+2)/2) ((lam+0+1)/2) (lam+3/2) (1/(x:ℂ)^2)‖)
      ≤ B1 * (Real.sqrt π * B2 * x^(-(ν.re-r)-1) * (MS * (1-1/x^2)^(-(1/4:ℝ)))) := by
        gcongr
    _ = Real.sqrt π * B1 * B2 * MS * ((1-1/x^2)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

/-- `λ ↦ 𝑄_λ(x)` is continuous at a regular `ν`, for `x > 1`. -/
theorem legPIU_continuousAt_Qext {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : 1 < x) :
    ContinuousAt (fun lam : ℂ => associatedQ lam 0 x) ν := by
  have hx0 : 0 < x := by linarith
  have hx0' : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have heq : (fun lam : ℂ => associatedQ lam 0 x) = fun lam => Gamma (lam+1) *
      ((Real.sqrt π : ℂ) * ((2:ℂ)^(lam+1))⁻¹ * ((x:ℂ)^(lam+1))⁻¹ *
        regularizedGaussHG ((lam+0+2)/2) ((lam+0+1)/2) (lam+3/2) (1/(x:ℂ)^2)) :=
    funext fun lam => legPIU_associatedQ_ext lam hx0
  rw [heq]
  have hz : 1/(x:ℂ)^2 ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
      div_lt_one (by positivity)]
    nlinarith
  have hG := (differentiable_regularizedGaussHG_comp (A := fun lam : ℂ => (lam+0+2)/2)
    (B := fun lam : ℂ => (lam+0+1)/2) (C := fun lam : ℂ => lam+3/2) (by fun_prop) (by fun_prop)
    (by fun_prop) hz).continuous.continuousAt (x := ν)
  refine ContinuousAt.mul (ContinuousAt.comp (g := Gamma) (f := fun l : ℂ => l + 1)
      (differentiableAt_Gamma _ (by simpa using legHyp_nu hν)).continuousAt (by fun_prop)) ?_
  refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_) hG
  · exact ((continuous_const_cpow' two_ne_zero |>.comp (continuous_id.add continuous_const)).inv₀
      (fun lam => cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))).continuousAt
  · exact ((continuous_const_cpow' hx0' |>.comp (continuous_id.add continuous_const)).inv₀
      (fun lam => cpow_ne_zero_iff.mpr (Or.inl hx0'))).continuousAt

/-- `(x-1)^{-1/2} x^p` is integrable on `(1,∞)` for `p < -1/2`. -/
theorem legPIU_integrableOn_weight {p : ℝ} (hp : p < -1/2) :
    IntegrableOn (fun x : ℝ => (x-1)^(-(1/2:ℝ)) * x^p) (Ioi 1) := by
  have hw : IntervalIntegrable (fun x : ℝ => (x-1)^(-(1/2:ℝ))) volume 1 2 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1/2:ℝ)) (by norm_num)
      (a := 0) (b := 1)).comp_sub_right 1
    norm_num at this ⊢; exact this
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun x : ℝ => (x-1)^(-(1/2:ℝ))) (Icc 1 2) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hw
    refine (h1.mul_continuousOn ?_ isCompact_Icc).mono_set Ioc_subset_Icc_self
    exact fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  · have hI := (integrableOn_Ioi_rpow_of_lt (a := p - 1/2) (by linarith) (by norm_num : (0:ℝ) < 2)).const_mul
      ((2:ℝ)^(1/2:ℝ))
    refine hI.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x (hx : 2 < x) => ?_) measurableSet_Ioi
      exact ((Real.continuousAt_rpow_const (x-1) _ (Or.inl (by linarith))).comp
        (f := fun y : ℝ => y - 1) (by fun_prop) |>.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith)))).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 2 < x) => ?_)
      have hx0 : 0 < x := by linarith
      have hx1 : 0 ≤ x - 1 := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx1 _) (Real.rpow_nonneg hx0.le _))]
      have h1 : (x-1)^(-(1/2:ℝ)) ≤ (x/2)^(-(1/2:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have h2 : (x/2)^(-(1/2:ℝ)) * x^p = (2:ℝ)^(1/2:ℝ) * x^(p-1/2) := by
        rw [Real.div_rpow hx0.le (by norm_num), show p - 1/2 = -(1/2:ℝ) + p by ring,
          Real.rpow_add hx0, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        field_simp
      calc _ ≤ (x/2)^(-(1/2:ℝ)) * x^p := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := h2

/-- legendre product integral 18. -/
@[dlmf 14.17.E18]
theorem legendre_product_integral_18 (ν : ℂ) (lam : ℂ) (hν : 0 < ν.re) (hlam : ν.re < lam.re) :
    HasIntegralAtTop (fun x : ℝ => associatedP ν 0 x*associatedQ lam 0 x) 1 (1/((lam-ν)*(ν+lam+1))) := by
  have hl0 : 0 < lam.re := by linarith
  have hr := legPI_regular_of_re_pos hl0
  have hd1 : ν - lam ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hd2 : ν + lam + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = (ν-lam)*(ν+lam+1) by ring]; exact mul_ne_zero hd1 hd2
  have hinf : Tendsto (fun x : ℝ => (lam+1)*associatedP ν 0 x*(x*associatedQ lam 0 x -
      associatedQ (lam+1) 0 x) - (ν+1)*associatedQ lam 0 x*(x*associatedP ν 0 x -
      associatedP (ν+1) 0 x)) atTop (𝓝 0) := by
    refine legExt_tendsto_zero_atTop (a := ν.re) (b := lam.re) hlam
      (legExt_associatedP_isBigO_atTop (by linarith)) ?_ (legExt_associatedQ_isBigO_atTop lam) ?_
    · have := legExt_associatedP_isBigO_atTop (ν := ν+1) (by simp; linarith)
      simpa using this
    · exact legExt_isBigO_rpow_mono (by simp) (legExt_associatedQ_isBigO_atTop (lam+1))
  have h1 := legExt_bdry (ν := ν) legExt_tendsto_half legExt_hx (legExt_P_isBigO ν) (legExt_Q_isBigO hr)
    (legExt_Q_isBigO_succ hr) (legExt_P_isBigO_succ ν)
    (by rw [legPI_cpos_succ hr]; ring) (by ring)
  have := legExt_integral_green (legExt_differentiableOn_P ν) (legExt_differentiableOn_Q lam)
    (legExt_ode_P ν) (legExt_ode_Q lam) (legExt_rec_P ν) (legExt_rec_Q hr)
    (fun R hR => legExt_intervalIntegrable_mul (legExt_continuousOn (legExt_differentiableOn_P ν))
      (legExt_continuousOn (legExt_differentiableOn_Q lam)) (legExt_P_isBigO ν)
      (legExt_Q_isBigO hr) hR) h1 hinf hc
  convert this using 1
  rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(ν+lam+1)) by ring]
  have : (lam - ν) ≠ 0 := fun h => hd1 (by linear_combination -h)
  field_simp
  ring

/-- legendre product integral 19. -/
@[dlmf 14.17.E19]
theorem legendre_product_integral_19 (ν : ℂ) (lam : ℂ) (h : -1 < (lam+ν).re) (hne : lam ≠ ν) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    HasIntegralAtTop (fun x : ℝ => associatedQ ν 0 x*associatedQ lam 0 x) 1 ((digamma (lam+1)-digamma (ν+1))/((lam-ν)*(lam+ν+1))) := by
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr hne
  have hd2 : lam + ν + 1 ≠ 0 := fun h' => by
    have := congrArg Complex.re h'; simp at this h; linarith
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  have hinf : Tendsto (fun x : ℝ => (lam+1)*associatedQ ν 0 x*(x*associatedQ lam 0 x -
      associatedQ (lam+1) 0 x) - (ν+1)*associatedQ lam 0 x*(x*associatedQ ν 0 x -
      associatedQ (ν+1) 0 x)) atTop (𝓝 0) := by
    refine legExt_tendsto_zero_atTop (a := -ν.re-1) (b := lam.re) (by simp at h; linarith)
      (legExt_associatedQ_isBigO_atTop ν) ?_ (legExt_associatedQ_isBigO_atTop lam) ?_
    · exact legExt_isBigO_rpow_mono (by simp) (legExt_associatedQ_isBigO_atTop (ν+1))
    · exact legExt_isBigO_rpow_mono (by simp) (legExt_associatedQ_isBigO_atTop (lam+1))
  have h1 := legExt_bdry (ν := ν) legExt_tendsto_half legExt_hx (legExt_Q_isBigO hν) (legExt_Q_isBigO hlam)
    (legExt_Q_isBigO_succ hlam) (legExt_Q_isBigO_succ hν)
    (by rw [legPI_cpos_succ hlam]; ring) (by rw [legPI_cpos_succ hν]; ring)
  have := legExt_integral_green (legExt_differentiableOn_Q ν) (legExt_differentiableOn_Q lam)
    (legExt_ode_Q ν) (legExt_ode_Q lam) (legExt_rec_Q hν) (legExt_rec_Q hlam)
    (fun R hR => legExt_intervalIntegrable_mul (legExt_continuousOn (legExt_differentiableOn_Q ν))
      (legExt_continuousOn (legExt_differentiableOn_Q lam)) (legExt_Q_isBigO hν)
      (legExt_Q_isBigO hlam) hR) h1 hinf hc
  convert this using 1
  rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
  unfold legPIcpos
  field_simp
  ring

/-- legendre product integral 20. -/
@[dlmf 14.17.E20]
theorem legendre_product_integral_20 (ν : ℂ) (hν : -1/2 < ν.re) :
    HasIntegralAtTop (fun x : ℝ => (associatedQ ν 0 x)^2) 1 (deriv digamma (ν+1)/(2*ν+1)) := by
  have hreg : LegendreQRegular ν 0 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hν1 := legHyp_nu hreg
  have h2ν : 2*ν+1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨r, hr, hrr0, M, hM0, hM⟩ := legPIU_bound_Qext hreg (r0 := (ν.re + 1/2)/2) (by linarith)
  set q := -(ν.re - r) - 3/4
  set g : ℝ → ℝ := fun x => M^2 * ((x-1)^(-(1/2:ℝ)) * x^(2*q))
  have hgI : IntegrableOn g (Ioi (1:ℝ)) := (legPIU_integrableOn_weight (p := 2*q) (by
    simp only [q]; linarith)).const_mul _
  have hQc : ∀ lam : ℂ, ContinuousOn (fun x : ℝ => associatedQ lam 0 x) (Ioi (1:ℝ)) :=
    fun lam => legExt_continuousOn (legExt_differentiableOn_Q lam)
  have hbd : ∀ lam : ℂ, ‖lam - ν‖ ≤ r → ∀ x : ℝ, 1 < x →
      ‖associatedQ ν 0 x * associatedQ lam 0 x‖ ≤ g x := by
    intro lam hl x hx
    have h1 := (hM ν (by simp; linarith)).2 x hx
    have h2 := (hM lam hl).2 x hx
    have hx1 : 0 < x - 1 := by linarith
    have hx0 : 0 < x := by linarith
    rw [norm_mul]
    calc _ ≤ (M * ((x-1)^(-(1/4:ℝ)) * x^q)) * (M * ((x-1)^(-(1/4:ℝ)) * x^q)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = g x := by
        simp only [g]
        rw [show (2*q) = q + q by ring, Real.rpow_add hx0,
          show (-(1/2:ℝ)) = -(1/4) + -(1/4) by norm_num, Real.rpow_add hx1]
        ring
  have hint : ∀ lam : ℂ, ‖lam - ν‖ ≤ r →
      IntegrableOn (fun x : ℝ => associatedQ ν 0 x * associatedQ lam 0 x) (Ioi (1:ℝ)) := by
    intro lam hl
    refine hgI.mono' (((hQc ν).mul (hQc lam)).aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hbd lam hl x hx)
  have hnear : ∀ᶠ lam in 𝓝 ν, ‖lam - ν‖ ≤ r := by
    filter_upwards [Metric.closedBall_mem_nhds ν hr] with lam hl
    rwa [Metric.mem_closedBall, dist_eq_norm] at hl
  -- dominated convergence on `(1,∞)`
  have hDCT : Tendsto (fun lam : ℂ => ∫ x : ℝ in Ioi 1, associatedQ ν 0 x * associatedQ lam 0 x) (𝓝 ν)
      (𝓝 (∫ x : ℝ in Ioi 1, associatedQ ν 0 x * associatedQ ν 0 x)) := by
    refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgI ?_
    · exact Eventually.of_forall fun lam =>
        ((hQc ν).mul (hQc lam)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [hnear] with lam hl
      exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hbd lam hl x hx)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_)
      exact tendsto_const_nhds.mul (legPIU_continuousAt_Qext hreg hx).tendsto
  -- the off-diagonal value
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hsl := hasDerivAt_iff_tendsto_slope.mp hψ'
  have hden : Tendsto (fun lam : ℂ => 1/(lam+ν+1)) (𝓝[≠] ν) (𝓝 (1/(ν+ν+1))) := by
    refine ((continuousAt_const.div ((continuousAt_id.add continuousAt_const).add
      continuousAt_const) ?_).tendsto).mono_left nhdsWithin_le_nhds
    show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν
  have hR := hsl.mul hden
  have hne : ∀ᶠ lam in 𝓝 ν, lam + ν + 1 ≠ 0 :=
    (show ContinuousAt (fun lam : ℂ => lam + ν + 1) ν by fun_prop).eventually_ne
      (by rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν)
  have heq : (fun lam : ℂ => ∫ x : ℝ in Ioi 1, associatedQ ν 0 x * associatedQ lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope (fun lam : ℂ => digamma (lam+1)) ν lam * (1/(lam+ν+1)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hne]
      with lam (h0 : lam ≠ ν) hl h1
    have hre : ν.re - r ≤ lam.re := by
      have := Complex.abs_re_le_norm (lam - ν)
      rw [sub_re] at this
      linarith [abs_le.mp (le_trans this hl)]
    have h19 := legendre_product_integral_19 ν lam (by simp; linarith) h0 hreg (hM lam hl).1
    have hI := intervalIntegral_tendsto_integral_Ioi 1 (hint lam hl) tendsto_id
    rw [tendsto_nhds_unique hI h19, slope_def_field]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    field_simp
  have hu := tendsto_nhds_unique ((hDCT.mono_left nhdsWithin_le_nhds).congr' heq) hR
  have hfin := intervalIntegral_tendsto_integral_Ioi 1 (hint ν (by simp; linarith)) tendsto_id
  unfold HasIntegralAtTop
  simp only [pow_two]
  rw [hu] at hfin
  rw [show deriv digamma (ν+1) * (1/(ν+ν+1)) = deriv digamma (ν+1)/(2*ν+1) by
    rw [show ν+ν+1 = 2*ν+1 by ring]; ring] at hfin
  exact hfin

end DLMF.Legendre
