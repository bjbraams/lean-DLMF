/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Asymptotics.ShiftedStirling

/-!
# Reciprocal-factorial expansions of Gamma ratios

Reciprocal-factorial Gamma-ratio expansions and the supporting coefficient identities.

Source references and common attribution are retained in
`DLMF.Gamma.Asymptotics`.
-/

@[expose] public section

open Complex Filter MeasureTheory

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Gamma

/-! ### The reciprocal-factorial expansion 5.11.19

For `Re (c - a) > 0` the remainder after `n` terms has the exact Beta-integral form
`Γ(t+b)/Γ(c-a) ∫₀^∞ s^{c-a-1} (1+s)^{-t-b} R_n(s) ds`, where `R_n` is the remainder of the
binomial series of `(1+s)^{b-c}` (`ratioThree_rem_eq`). The Taylor bound
`|R_n(s)| ≤ K sⁿ (1+s)^M` and the real Beta integral then give the `O`-bound. The restriction
on `a` is removed by the exact shift identity `ratioThreeSum_shift`, which lowers `a` by one
at the cost of a factor `t` and one extra reciprocal-factorial term.
-/

section RatioThree

open Set

/-- The binomial coefficient `β(β-1)⋯(β-k+1)/k!`, written with a Pochhammer symbol. -/
def recipFacBinom (β : ℂ) (k : ℕ) : ℂ := (-1) ^ k * poch (-β) k / k.factorial

/-- The remainder of the binomial series of `(1+s)^β` after `n` terms. -/
def recipFacRem (β : ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  (1 + (s : ℂ)) ^ β - ∑ k ∈ Finset.range n, recipFacBinom β k * (s : ℂ) ^ k

/-- The zeroth binomial coefficient `C(β, 0) = 1`. -/
theorem recipFacBinom_zero (β : ℂ) : recipFacBinom β 0 = 1 := by simp [recipFacBinom, poch_zero]

/-- `(a)_{n+1} = a (a + 1)_n`. -/
theorem poch_succ_left' (a : ℂ) (n : ℕ) : poch a (n + 1) = a * poch (a + 1) n := by
  simp [poch, ascPochhammer_succ_left, Polynomial.eval_comp, add_comm]

/-- `C(β, k + 1)(k + 1) = β C(β - 1, k)`. -/
theorem recipFacBinom_succ (β : ℂ) (k : ℕ) :
    recipFacBinom β (k + 1) * (k + 1) = β * recipFacBinom (β - 1) k := by
  simp only [recipFacBinom, poch_succ_left', Nat.factorial_succ]
  rw [show -β + 1 = -(β - 1) by ring]
  push_cast
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  field_simp
  ring

/-- `1 + s` lies in the slit plane for real `s > -1`. -/
theorem one_add_ofReal_mem_slitPlane {s : ℝ} (hs : -1 < s) : 1 + (s : ℂ) ∈ slitPlane := by
  rw [show 1 + (s : ℂ) = ((1 + s : ℝ) : ℂ) by push_cast; ring]
  exact ofReal_mem_slitPlane.mpr (by linarith)

/-- `u ↦ (1 + u)^β` has derivative `β (1 + s)^(β-1)` at real `s > -1`. -/
theorem hasDerivAt_one_add_cpow (β : ℂ) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (fun u : ℝ => (1 + (u : ℂ)) ^ β) (β * (1 + (s : ℂ)) ^ (β - 1)) s := by
  have h := ((hasDerivAt_id (s : ℂ)).const_add 1).cpow_const (c := β)
    (one_add_ofReal_mem_slitPlane hs)
  simpa using h.comp_ofReal

/-- The remainder of the binomial series of `(1 + s)^β` after `n + 1` terms has derivative `β` times
the remainder of `(1 + s)^(β-1)` after `n` terms. -/
theorem hasDerivAt_recipFacRem (β : ℂ) (n : ℕ) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (recipFacRem β (n + 1)) (β * recipFacRem (β - 1) n s) s := by
  have hp : ∀ k ∈ Finset.range (n + 1), HasDerivAt
      (fun u : ℝ => recipFacBinom β k * (u : ℂ) ^ k)
      (recipFacBinom β k * ((k : ℂ) * (s : ℂ) ^ (k - 1))) s := fun k _ =>
    ((hasDerivAt_pow k (s : ℂ)).comp_ofReal).const_mul _
  have h := (hasDerivAt_one_add_cpow β hs).sub (HasDerivAt.fun_sum hp)
  convert h using 1
  · funext u; rfl
  rw [recipFacRem, Finset.sum_range_succ', mul_sub, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← recipFacBinom_succ]
  push_cast
  ring

/-- The binomial remainder after `n + 1` terms vanishes at `s = 0`. -/
theorem recipFacRem_zero_right (β : ℂ) (n : ℕ) : recipFacRem β (n + 1) 0 = 0 := by
  rw [recipFacRem, Finset.sum_range_succ']
  simp [recipFacBinom_zero]

/-- The binomial remainder is continuous on `(-1, ∞)`. -/
theorem continuousOn_recipFacRem (β : ℂ) (n : ℕ) : ContinuousOn (recipFacRem β n) (Ioi (-1)) := by
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.sub ?_ (by fun_prop)
  exact ContinuousAt.cpow (by fun_prop) continuousAt_const (one_add_ofReal_mem_slitPlane hs)

/-- The binomial remainder after `n` terms is bounded by `K sⁿ (1 + s)^max(Re β, 0)` for `s ≥ 0`. -/
theorem exists_norm_recipFacRem_le (n : ℕ) : ∀ β : ℂ, ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s →
    ‖recipFacRem β n s‖ ≤ K * s ^ n * (1 + s) ^ max β.re 0 := by
  induction n with
  | zero =>
    intro β
    refine ⟨1, zero_le_one, fun s hs => ?_⟩
    have h1 : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    simp only [recipFacRem, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, one_mul]
    rw [h1, norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  | succ n ih =>
    intro β
    obtain ⟨K, hK, hb⟩ := ih (β - 1)
    refine ⟨‖β‖ * K, by positivity, fun s hs => ?_⟩
    have hderiv : ∀ u ∈ uIcc 0 s, HasDerivAt (recipFacRem β (n + 1))
        (β * recipFacRem (β - 1) n u) u := by
      intro u hu
      rw [uIcc_of_le hs] at hu
      exact hasDerivAt_recipFacRem β n (by linarith [hu.1])
    have hcont : ContinuousOn (fun u => β * recipFacRem (β - 1) n u) (uIcc 0 s) := by
      refine continuousOn_const.mul ((continuousOn_recipFacRem _ n).mono fun u hu => ?_)
      rw [uIcc_of_le hs] at hu
      exact show -1 < u by linarith [hu.1]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable)
    rw [recipFacRem_zero_right, sub_zero] at hftc
    rw [← hftc]
    have hle : ∀ u ∈ Set.uIoc (0 : ℝ) s, ‖β * recipFacRem (β - 1) n u‖ ≤
        ‖β‖ * K * s ^ n * (1 + s) ^ max β.re 0 := by
      intro u hu
      rw [uIoc_of_le hs] at hu
      have hu0 : 0 ≤ u := hu.1.le
      rw [norm_mul, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (hb u hu0).trans ?_
      rw [← mul_assoc]
      have hre : max (β - 1).re 0 ≤ max β.re 0 := by
        simp only [sub_re, one_re]; exact max_le_max (by linarith) le_rfl
      have hpow : (1 + u) ^ max (β - 1).re 0 ≤ (1 + s) ^ max β.re 0 :=
        (Real.rpow_le_rpow (by linarith) (by linarith [hu.2]) (le_max_right _ _)).trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hre)
      have hun : u ^ n ≤ s ^ n := pow_le_pow_left₀ hu0 hu.2 n
      gcongr
    calc ‖∫ u in (0 : ℝ)..s, β * recipFacRem (β - 1) n u‖
        ≤ ‖β‖ * K * s ^ n * (1 + s) ^ max β.re 0 * |s - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hle
      _ = ‖β‖ * K * s ^ (n + 1) * (1 + s) ^ max β.re 0 := by
          rw [sub_zero, abs_of_nonneg hs]; ring

/-- `s^(p-1) (1 + s)^(-A)` is integrable on `(0, ∞)` when `0 < Re p < Re A`. -/
theorem integrableOn_cpow_mul_one_add_cpow {p A : ℂ} (hp : 0 < p.re) (hpA : p.re < A.re) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (p - 1) * ((1 + s : ℝ) : ℂ) ^ (-A)) (Ioi 0) := by
  have hg := integrableOn_rpow_mul_one_add_rpow hp hpA
  have hcont : ContinuousOn (fun s : ℝ => (s : ℂ) ^ (p - 1) * ((1 + s : ℝ) : ℂ) ^ (-A))
      (Ioi 0) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
        (ofReal_mem_slitPlane.mpr hs0)
    · exact ContinuousAt.cpow (continuous_ofReal.continuousAt.comp
        (continuousAt_const.add continuousAt_id)) continuousAt_const
        (ofReal_mem_slitPlane.mpr (by linarith))
  refine hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs0, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp

/-- `Γ(α + k) = (α)ₖ Γ(α)` for `Re α > 0`. -/
theorem Gamma_add_nat_eq_poch_mul_Gamma {α : ℂ} (hα : 0 < α.re) (k : ℕ) :
    Complex.Gamma (α + k) = poch α k * Complex.Gamma α := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have hne : α + k ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih, poch_succ]
    ring

/-- The Beta-integral representation of the remainder of the reciprocal-factorial expansion. -/
theorem ratioThree_rem_eq {a b c : ℂ} (n : ℕ) (hα : 0 < (c - a).re) {t : ℝ}
    (hta : 0 < (t + a).re) (htb : (c - a).re + n < (t + b).re) :
    Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
            Complex.Gamma (a + b - c + t - k) =
      Complex.Gamma (t + b) / Complex.Gamma (c - a) *
        ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (c - a - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)) *
          recipFacRem (b - c) n s := by
  set α := c - a with hαdef
  have htb0 : 0 < (t + b).re := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hΓα : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  have hΓb : Complex.Gamma (t + b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos htb0
  have hαc : α.re < (t + c).re := by
    have : (t + c).re = (t + a).re + α.re := by
      simp only [hαdef, add_re, sub_re]; ring
    linarith
  have hk : ∀ k ∈ Finset.range n, (α + k).re < (t + b).re := by
    intro k hk
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
    have h2 := htb
    simp only [add_re, natCast_re, ofReal_re] at h2 ⊢
    linarith
  have hkpos : ∀ k : ℕ, 0 < (α + k).re := by
    intro k; simp only [add_re, natCast_re]; positivity
  -- the integrals
  have hF := mellin_one_add_cpow_neg (a := t + c) (s := α) hα hαc
  have hK : ∀ k ∈ Finset.range n,
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (α + k - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)) =
        Complex.Gamma (α + k) * Complex.Gamma (t + b - (α + k)) / Complex.Gamma (t + b) := by
    intro k hk'
    have := mellin_one_add_cpow_neg (a := t + b) (s := α + k) (hkpos k) (hk k hk')
    rw [mellin] at this
    simpa only [smul_eq_mul] using this
  rw [mellin] at hF
  simp only [smul_eq_mul] at hF
  -- pointwise identity of integrands
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      (s : ℂ) ^ (α - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)) * recipFacRem (b - c) n s =
        (s : ℂ) ^ (α - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + c)) -
          ∑ k ∈ Finset.range n, recipFacBinom (b - c) k *
            ((s : ℂ) ^ (α + k - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b))) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
    have h1 : ((1 + s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 + s : ℝ) ≠ 0 by linarith)
    have hc1 : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    have hpow : ((1 + s : ℝ) : ℂ) ^ (-(t + c)) =
        ((1 + s : ℝ) : ℂ) ^ (-(t + b)) * ((1 + s : ℝ) : ℂ) ^ (b - c) := by
      rw [← cpow_add _ _ h1]; congr 1; ring
    have hspow : ∀ k : ℕ, (s : ℂ) ^ (α + k - 1) = (s : ℂ) ^ (α - 1) * (s : ℂ) ^ k := by
      intro k
      rw [← cpow_natCast, ← cpow_add _ _ hs0]; congr 1; ring
    rw [recipFacRem, hc1, hpow, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hspow]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hintF := integrableOn_cpow_mul_one_add_cpow (p := α) (A := t + c) hα hαc
  have hintK : ∀ k ∈ Finset.range n, Integrable (fun s : ℝ => recipFacBinom (b - c) k *
      ((s : ℂ) ^ (α + k - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)))) (volume.restrict (Ioi 0)) :=
    fun k hk' => (integrableOn_cpow_mul_one_add_cpow (hkpos k) (hk k hk')).const_mul _
  rw [integral_sub hintF (integrable_finsetSum _ hintK), integral_finsetSum _ hintK, hF]
  simp_rw [integral_const_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · rw [show t + c - α = t + a by rw [hαdef]; ring]
    field_simp
  · refine Finset.sum_congr rfl fun k hk' => ?_
    rw [hK k hk', Gamma_add_nat_eq_poch_mul_Gamma hα, recipFacBinom,
      show -(b - c) = c - b by ring, show t + b - (α + k) = a + b - c + t - k by
        simp [hαdef]; ring]
    field_simp

/-- The norm bound on the Beta-integral remainder. -/
theorem norm_integral_recipFacRem_le {α β B : ℂ} {n : ℕ} {K M : ℝ}
    (hb : ∀ s : ℝ, 0 ≤ s → ‖recipFacRem β n s‖ ≤ K * s ^ n * (1 + s) ^ M)
    (hα : 0 < α.re) (hB : α.re + n + M < B.re) :
    ‖∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (α - 1) * ((1 + s : ℝ) : ℂ) ^ (-B) * recipFacRem β n s‖ ≤
      K * (Real.Gamma (α.re + n) * Real.Gamma (B.re - M - (α.re + n)) /
        Real.Gamma (B.re - M)) := by
  set p : ℝ := α.re + n with hp
  set q : ℝ := B.re - M - p with hq
  have hp0 : 0 < p := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨hint, hval⟩ := real_beta_on_Ioi hp0 hq0
  have hpq : p + q = B.re - M := by ring
  rw [hpq] at hint hval
  rw [← hval, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul K) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  have h1 : (0 : ℝ) < 1 + s := by linarith
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hs0, norm_cpow_eq_rpow_re_of_pos h1]
  have hr := hb s hs0.le
  calc s ^ (α - 1).re * (1 + s) ^ (-B).re * ‖recipFacRem β n s‖
      ≤ s ^ (α - 1).re * (1 + s) ^ (-B).re * (K * s ^ n * (1 + s) ^ M) := by gcongr
    _ = K * (s ^ (p - 1) / (1 + s) ^ (B.re - M)) := by
      have e1 : s ^ (p - 1) = s ^ (α - 1).re * s ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; congr 1; simp [hp]; ring
      have e2 : (1 + s) ^ (-B).re * (1 + s) ^ M = ((1 + s) ^ (B.re - M))⁻¹ := by
        rw [← Real.rpow_add h1, ← Real.rpow_neg h1.le]; congr 1; simp; ring
      rw [e1, div_eq_mul_inv, ← e2]; ring

/-- The partial sum of the reciprocal-factorial expansion 5.11.19. -/
def ratioThreeSum (a b c : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
    Complex.Gamma (a + b - c + t - k)

/-- The boundary coefficient in the shift identity `ratioThreeSum_shift`. -/
def ratioThreeShiftCoeff (a b c : ℂ) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (-1 : ℂ) ^ j * poch (c - a + 1) j * poch (c - b) (j + 1) / j.factorial

/-- Shift identity for the partial sums of 5.11.19 in the parameter `a`. -/
theorem ratioThreeSum_shift (a b c : ℂ) (t : ℝ) (n : ℕ)
    (hne : ∀ k < n, a + b - c + t - 1 - k ≠ 0) :
    ((t : ℂ) + a - 1) * ratioThreeSum (a - 1) b c n t =
      ratioThreeSum a b c n t + ratioThreeShiftCoeff a b c n *
        Complex.Gamma (a + b - c + t - n) := by
  induction n with
  | zero => simp [ratioThreeSum, ratioThreeShiftCoeff]
  | succ n ih =>
    have ih' := ih fun k hk => hne k (by omega)
    simp only [ratioThreeSum, Finset.sum_range_succ] at ih' ⊢
    set Y : ℂ := a + b - c + t - 1 - n with hY
    have hYne : Y ≠ 0 := hne n (by omega)
    have hX1 : a - 1 + b - c + t - n = Y := by rw [hY]; ring
    have hX2 : a + b - c + t - ((n + 1 : ℕ) : ℂ) = Y := by rw [hY]; push_cast; ring
    have hX3 : a + b - c + t - n = Y + 1 := by rw [hY]; ring
    have hG : Complex.Gamma (Y + 1) = Y * Complex.Gamma Y := Complex.Gamma_add_one Y hYne
    rw [mul_add, ih', hX1, hX2, hX3, hG]
    have hc : c - (a - 1) = c - a + 1 := by ring
    rw [hc]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rcases n with _ | j
    · simp only [ratioThreeShiftCoeff, poch_zero, poch_one, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul, zero_mul, add_zero, Finset.range_zero,
        Finset.sum_empty, zero_add, Nat.cast_zero] at hY ⊢
      rw [hY]; ring
    · simp only [ratioThreeShiftCoeff]
      rw [poch_succ_left' (c - a) j, poch_succ (c - a + 1) j,
        poch_succ (c - b) (j + 1), Nat.factorial_succ]
      rw [hY]
      have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
      push_cast
      field_simp
      ring

/-- The leading-order consequence of 5.11.13: `Γ(t+u)/Γ(t+v) = O(t^{u-v})`. -/
theorem isBigO_Gamma_add_div_Gamma_add (u v : ℂ) :
    (fun t : ℝ => Complex.Gamma (t + u) / Complex.Gamma (t + v)) =O[atTop]
      fun t : ℝ => (t : ℂ) ^ (u - v) := by
  have h := Gamma_ratio_expansion u v 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, div_one, Nat.cast_one,
    stirlingRatioG_zero, mul_one] at h
  have h1 : (fun t : ℝ => (t : ℂ) ^ (u - v - 1)) =O[atTop] fun t : ℝ => (t : ℂ) ^ (u - v) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [one_mul, norm_cpow_eq_rpow_re_of_pos (by linarith),
      norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le ht (by simp)
  exact ((h.trans h1).add (Asymptotics.isBigO_refl (fun t : ℝ => (t : ℂ) ^ (u - v)) atTop))
    |>.congr_left fun t => by ring

/-- 5.11.19 when `Re (c - a) > 0`, via the Beta-integral remainder. -/
theorem ratioThree_isBigO_of_re_pos {a b c : ℂ} (n : ℕ) (hα : 0 < (c - a).re) :
    (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n) := by
  obtain ⟨K, hK0, hb⟩ := exists_norm_recipFacRem_le n (b - c)
  set M : ℝ := max (b - c).re 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  set p : ℝ := (c - a).re + n with hpdef
  have hp0 : 0 < p := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  set u1 : ℝ := b.re - M - p with hu1
  set v1 : ℝ := b.re - M with hv1
  set C : ℝ := K * Real.Gamma p / ‖Complex.Gamma (c - a)‖ with hC
  have hΓα : Complex.Gamma (c - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  -- the pointwise bound
  have hbound : ∀ᶠ t : ℝ in atTop, ‖Complex.Gamma (t + a) * Complex.Gamma (t + b) /
      Complex.Gamma (t + c) - ratioThreeSum a b c n t‖ ≤
      C * ‖Complex.Gamma (t + b) / Complex.Gamma (t + 0) * Complex.Gamma t *
        (Complex.Gamma ((t : ℂ) + (u1 : ℂ)) / Complex.Gamma ((t : ℂ) + (v1 : ℂ)))‖ := by
    filter_upwards [eventually_gt_atTop (max (max 0 (-a.re)) (max (p + M - b.re) (-u1)))]
      with t ht
    simp only [max_lt_iff] at ht
    obtain ⟨⟨ht0, hta⟩, htb, htu⟩ := ht
    have hta' : 0 < ((t : ℂ) + a).re := by simp; linarith
    have htbre : ((t : ℂ) + b).re = t + b.re := by simp
    have htb' : (c - a).re + n < ((t : ℂ) + b).re := by rw [htbre]; linarith
    have hB : (c - a).re + n + M < ((t : ℂ) + b).re := by rw [htbre]; linarith
    have hrem := ratioThree_rem_eq (a := a) (b := b) (c := c) n hα hta' htb'
    have hJ := norm_integral_recipFacRem_le (α := c - a) (β := b - c) (B := t + b) (n := n)
      (K := K) (M := M) hb hα hB
    rw [htbre] at hJ
    have e1 : t + b.re - M - ((c - a).re + n) = t + u1 := by rw [hu1, hpdef]; ring
    have e2 : t + b.re - M = t + v1 := by rw [hv1]; ring
    rw [e1, e2] at hJ
    have htu1 : 0 < t + u1 := by linarith
    have htv1 : 0 < t + v1 := by linarith
    have hΓt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht0)
    have hcast : ∀ x : ℝ, Complex.Gamma ((t : ℂ) + (x : ℂ)) = (Real.Gamma (t + x) : ℂ) := by
      intro x; rw [← Complex.ofReal_add, Complex.Gamma_ofReal]
    rw [hcast, hcast, ← Complex.ofReal_div, add_zero, div_mul_cancel₀ _ hΓt, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.Gamma_pos_of_pos htu1) (Real.Gamma_pos_of_pos htv1))]
    unfold ratioThreeSum
    rw [hrem, norm_mul, norm_div, hC]
    calc ‖Complex.Gamma (t + b)‖ / ‖Complex.Gamma (c - a)‖ * ‖∫ s in Ioi (0 : ℝ),
          (s : ℂ) ^ (c - a - 1) * ((1 + s : ℝ) : ℂ) ^ (-((t : ℂ) + b)) *
            recipFacRem (b - c) n s‖
        ≤ ‖Complex.Gamma (t + b)‖ / ‖Complex.Gamma (c - a)‖ *
          (K * (Real.Gamma p * Real.Gamma (t + u1) / Real.Gamma (t + v1))) := by
          gcongr
      _ = K * Real.Gamma p / ‖Complex.Gamma (c - a)‖ * (‖Complex.Gamma (t + b)‖ *
          (Real.Gamma (t + u1) / Real.Gamma (t + v1))) := by ring
  have h1 := Asymptotics.IsBigO.of_bound C hbound
  have h2 := ((isBigO_Gamma_add_div_Gamma_add b 0).mul
    (Asymptotics.isBigO_refl (fun t : ℝ => Complex.Gamma t) atTop)).mul
      (isBigO_Gamma_add_div_Gamma_add u1 v1)
  refine h1.trans (h2.trans (Asymptotics.IsBigO.of_bound 1 ?_))
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [one_mul, norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
    norm_cpow_eq_rpow_re_of_pos ht, norm_cpow_eq_rpow_re_of_pos ht]
  have he : (b - 0).re + ((u1 : ℂ) - (v1 : ℂ)).re = (a + b - c - n).re := by
    simp only [sub_re, ofReal_re, add_re, natCast_re, zero_re, hu1, hv1, hpdef]
    ring
  rw [← he, Real.rpow_add ht]
  apply le_of_eq
  ring

/-- Lowering `a` by one in 5.11.19 costs one factor `t` and adds one reciprocal-factorial term. -/
theorem ratioThree_isBigO_shift {a b c : ℂ} (n : ℕ)
    (h : (fun t : ℝ => Complex.Gamma (t + (a - 1)) * Complex.Gamma (t + b) /
        Complex.Gamma (t + c) - ratioThreeSum (a - 1) b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a - 1 + b - c - n)) :
    (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n) := by
  set w : ℂ := a + b - c - n with hw
  set e : ℂ := ratioThreeShiftCoeff a b c n
  have heq : (fun t : ℝ => ((t : ℂ) + a - 1) * (Complex.Gamma (t + (a - 1)) *
      Complex.Gamma (t + b) / Complex.Gamma (t + c) - ratioThreeSum (a - 1) b c n t) +
        e * Complex.Gamma (a + b - c + t - n)) =ᶠ[atTop]
      fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t := by
    filter_upwards [eventually_gt_atTop (max (1 - a.re) (n + 1 - (a + b - c).re))]
      with t ht
    simp only [max_lt_iff] at ht
    have hne1 : (t : ℂ) + (a - 1) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hne : ∀ k < n, a + b - c + t - 1 - k ≠ 0 := by
      intro k hk h0
      have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      have := congrArg Complex.re h0
      have h2 := ht.2
      simp only [sub_re, add_re] at h2
      simp at this
      linarith
    have hG : Complex.Gamma (t + a) = ((t : ℂ) + (a - 1)) * Complex.Gamma (t + (a - 1)) := by
      rw [← Complex.Gamma_add_one _ hne1]; congr 1; ring
    rw [mul_sub, ratioThreeSum_shift a b c t n hne, hG]
    ring
  have hlin : (fun t : ℝ => (t : ℂ) + a - 1) =O[atTop] fun t : ℝ => (t : ℂ) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop ‖a - 1‖, eventually_ge_atTop 0] with t ht ht0
    rw [show (t : ℂ) + a - 1 = t + (a - 1) by ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    calc ‖(t : ℂ) + (a - 1)‖ ≤ ‖(t : ℂ)‖ + ‖a - 1‖ := norm_add_le _ _
      _ ≤ 2 * t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; linarith
  have hA := hlin.mul h
  have hA' : (fun t : ℝ => (t : ℂ) * (Complex.Gamma t * (t : ℂ) ^ (a - 1 + b - c - n)))
      =ᶠ[atTop] fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ w := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [show w = (a - 1 + b - c - n) + 1 by rw [hw]; ring, cpow_add _ _ ht0, cpow_one]
    ring
  have hB : (fun t : ℝ => e * Complex.Gamma (a + b - c + t - n)) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ w := by
    have h3 := (((isBigO_Gamma_add_div_Gamma_add w 0).mul
      (Asymptotics.isBigO_refl (fun t : ℝ => Complex.Gamma t) atTop)).const_mul_left e)
    refine (h3.congr' ?_ ?_)
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hΓt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
      rw [add_zero, div_mul_cancel₀ _ hΓt, show (t : ℂ) + w = a + b - c + t - n by
        rw [hw]; ring]
    · filter_upwards with t
      rw [sub_zero, mul_comm]
  exact ((hA.trans_eventuallyEq hA').add hB).congr' heq EventuallyEq.rfl

/-- Inductive core of the remainder bound for 5.11.19: the error of the `n`-term
reciprocal-factorial expansion of `Γ(t + a)Γ(t + b)/Γ(t + c)` is `O(Γ(t) t^(a+b-c-n))`, by induction
on `m` with `Re(c - a) + m > 0`. -/
lemma ratioThree_isBigO_aux {b c : ℂ} (n : ℕ) (m : ℕ) : ∀ a : ℂ, 0 < (c - a).re + m →
    (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n) := by
  induction m with
  | zero => intro a ha; exact ratioThree_isBigO_of_re_pos n (by simpa using ha)
  | succ m ih =>
    intro a ha
    refine ratioThree_isBigO_shift n (ih (a - 1) ?_)
    simp only [sub_re, one_re] at ha ⊢
    push_cast at ha
    linarith

end RatioThree

/-- The reciprocal-factorial Gamma-ratio expansion. The remainder retains the
parameter-dependent leading power `a + b - c`, which cannot be omitted. -/
@[dlmf 5.11.E19]
theorem Gamma_ratio_three {a b c : ℂ} (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
            Complex.Gamma (a + b - c + t - k))
      (fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-(c - a).re)
  exact ratioThree_isBigO_aux n m a (by linarith)

end DLMF.Gamma

end
end
