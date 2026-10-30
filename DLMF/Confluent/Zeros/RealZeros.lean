/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.KummerProperties
public import DLMF.ErrorFunctions.ZeroTools
public import DLMF.Confluent.ZeroTools

/-!
# Counts of real Kummer zeros

Positive real zero counts of Kummer functions obtained from differential-equation comparison.

Source references and common attribution are retained in
`DLMF.Confluent.Zeros`.
-/

@[expose] public section

open Complex Filter Set

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Positive real zeros of `M(a,b,·)`. -/
def kummerMPosZeros (a b : ℝ) : Set ℝ :=
  {x | 0 < x ∧ kummerM a b x = 0}

/-- Positive real zeros of `U(a,b,·)`. -/
def kummerUPosZeros (a b : ℝ) : Set ℝ :=
  {x | 0 < x ∧ kummerU a b x = 0}

/-- The boundary case omitted by the positive-zero formulas: `M(0,b,x) = 1`. -/
theorem kummerM_posZeros_zero (b : ℝ) : (kummerMPosZeros 0 b).encard = 0 := by
  simp [kummerMPosZeros, kummerM_of_zero_param]

/-- Kummer's series has positive real part for nonnegative real numerator and
positive real argument, including its totalized denominator value at zero. -/
theorem kummerM_re_pos_of_nonneg {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 < x) : 0 < (kummerM a b x).re := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · have h : kummerM (a : ℂ) 0 x = 1 := by
      unfold kummerM
      rw [tsum_eq_single 0]
      · simp [poch_zero]
      · intro n hn
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp only [Nat.succ_eq_add_one, poch_zero_succ, zero_mul, div_zero]
    simp [h]
  · have hb' : ∀ k : ℕ, (b : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simpa using hb)
    have hs := (hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hb').hasSum_mul_pow
      (z := (x : ℂ)) (by simp)
    have hr := Complex.hasSum_re hs
    let t : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval a /
      ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n
    have ht : ∀ n : ℕ, (kummerMCoeff (a : ℂ) b n * (x : ℂ) ^ n).re = t n := by
      intro n
      simp [t, kummerMCoeff, poch_ofReal, ← ofReal_natCast, ← ofReal_mul,
        ← ofReal_div, ← ofReal_pow]
    simp only [ht] at hr
    have hnonneg : ∀ n, 0 ≤ t n := fun n => mul_nonneg
      (div_nonneg (poch_eval_nonneg ha n)
        (mul_nonneg (poch_eval_nonneg hb.le n) (Nat.cast_nonneg _)))
      (pow_nonneg hx.le n)
    have hle := hr.summable.sum_le_tsum ({0} : Finset ℕ) (fun n _ => hnonneg n)
    have h0 : t 0 = 1 := by simp [t]
    rw [Finset.sum_singleton, h0, hr.tsum_eq] at hle
    linarith

/-- Identity under the stated parameter and domain assumptions: `(kummerMPosZeros a b).encard =
0`. -/
@[dlmf 13.9.E2]
theorem kummerM_posZeros_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (kummerMPosZeros a b).encard = 0 := by
  rw [Set.encard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hzero⟩
  have hp := kummerM_re_pos_of_nonneg ha hb hx
  rw [hzero] at hp
  simp at hp

/-- For real parameters with `b ∉ -ℕ`, Kummer's series at a real point is real: it is the
complexification of the real power series. -/
theorem kummerM_ofReal_hasSum {a b : ℝ} (hb : ∀ k : ℕ, (b : ℂ) ≠ -k) (x : ℝ) :
    HasSum (fun n => (ascPochhammer ℝ n).eval a /
        ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n) (kummerM a b x).re ∧
      kummerM a b x = ((kummerM a b x).re : ℂ) := by
  let t : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval a /
    ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n
  have hs := (hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hb).hasSum_mul_pow
    (z := (x : ℂ)) (by simp)
  have ht : ∀ n : ℕ, kummerMCoeff (a : ℂ) b n * (x : ℂ) ^ n = (t n : ℂ) := by
    intro n
    simp [t, kummerMCoeff, poch_ofReal]
  simp only [ht] at hs
  have hr : HasSum t (kummerM a b x).re := by
    simpa using Complex.hasSum_re hs
  refine ⟨hr, ?_⟩
  exact hs.unique (Complex.hasSum_ofReal.mpr hr)

/-! ### Counting positive real zeros (DLMF 13.9.1, 13.9.4–13.9.6)

The counts are proved by induction along `(a,b) ↦ (a+1,b+1)` using `M' = (a/b) M(a+1,b+1,·)`
and Kummer's equation, which at a zero `x` of `M(a+1,b+1,·)` gives
`M(a,b,x) = (x/b) M'(a+1,b+1,x)`. The invariant `kumZ_Q` records the zeros together with the
sign pattern between them and the eventual growth. -/

/-- Sign-pattern data for counting positive zeros: `f` has exactly `m` positive zeros
`y 1 < ⋯ < y m`, at which `(-1)^j f'` is positive, with `(-1)^j f > 0` between consecutive zeros,
`(-1)^m f > 0` beyond the last one, and eventually `(-1)^m f ≥ 1`. -/
def kumZ_Q (f f' : ℝ → ℝ) (m : ℕ) : Prop :=
  ∃ y : ℕ → ℝ, y 0 = 0 ∧ (∀ j < m, y j < y (j + 1)) ∧
    (∀ j, 1 ≤ j → j ≤ m → f (y j) = 0 ∧ 0 < (-1) ^ j * f' (y j)) ∧
    (∀ j < m, ∀ x ∈ Ioo (y j) (y (j + 1)), 0 < (-1) ^ j * f x) ∧
    (∀ x, y m < x → 0 < (-1) ^ m * f x) ∧
    (∃ X, ∀ x, X ≤ x → 1 ≤ (-1) ^ m * f x)

/-- The base case: a function bounded below by `1` on `[0, ∞)` has no positive zeros. -/
theorem kumZ_Q_zero {f f' : ℝ → ℝ} (h1 : ∀ x, 0 ≤ x → 1 ≤ f x) : kumZ_Q f f' 0 := by
  refine ⟨fun j => j, by simp, fun j hj => absurd hj (Nat.not_lt_zero _),
    fun j hj1 hj => by omega, fun j hj => absurd hj (Nat.not_lt_zero _), fun x hx => ?_,
    ⟨0, fun x hx => by simpa using h1 x hx⟩⟩
  have := h1 x (by simp at hx; linarith)
  simp only [pow_zero, one_mul]; linarith

/-- Under `kumZ_Q`, the positive zeros are exactly `y 1, …, y m`. -/
theorem kumZ_Q_encard {f f' : ℝ → ℝ} {m : ℕ} (hQ : kumZ_Q f f' m) :
    {x : ℝ | 0 < x ∧ f x = 0}.encard = m := by
  obtain ⟨y, hy0, hymono, hyz, hysign, hylast, -⟩ := hQ
  have hmono : StrictMonoOn y (Iic m) := strictMonoOn_Iic_of_lt_succ fun j hj => hymono j hj
  have hset : {x : ℝ | 0 < x ∧ f x = 0} = y '' Icc 1 m := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      have hxm : x ≤ y m := by
        by_contra h
        push Not at h
        have := hylast x h
        rw [hfx, mul_zero] at this
        exact lt_irrefl _ this
      have hex : ∃ j, x ≤ y j := ⟨m, hxm⟩
      classical
      let j := Nat.find hex
      have hj : x ≤ y j := Nat.find_spec hex
      have hjm : j ≤ m := Nat.find_min' hex hxm
      have hj1 : 1 ≤ j := by
        by_contra h
        have : j = 0 := by omega
        rw [this, hy0] at hj
        linarith
      have hprev : y (j - 1) < x := by
        have := Nat.find_min hex (show j - 1 < j by omega)
        push Not at this
        exact this
      rcases hj.lt_or_eq with hlt | heq
      · have := hysign (j - 1) (by omega) x ⟨hprev, by rwa [show j - 1 + 1 = j by omega]⟩
        rw [hfx, mul_zero] at this
        exact absurd this (lt_irrefl _)
      · exact ⟨j, ⟨hj1, hjm⟩, heq.symm⟩
    · rintro ⟨j, ⟨hj1, hjm⟩, rfl⟩
      refine ⟨?_, (hyz j hj1 hjm).1⟩
      have := hmono (show 0 ∈ Iic m from Nat.zero_le m) (show j ∈ Iic m from hjm)
        (by omega)
      rwa [hy0] at this
  rw [hset, (hmono.mono Icc_subset_Iic_self).injOn.encard_image]
  have : (Icc 1 m : Set ℕ) = ((Finset.Icc 1 m : Finset ℕ) : Set ℕ) := by simp
  rw [this, Set.encard_coe_eq_coe_finsetCard]
  simp

/-- A strictly increasing continuous function on an order-connected set, negative at its least
point and positive somewhere, has exactly one zero there, with the expected signs. -/
theorem kumZ_unique_zero {h : ℝ → ℝ} {S : Set ℝ} {p : ℝ} (hS : S.OrdConnected) (hp : p ∈ S)
    (hc : ContinuousOn h S) (hm : StrictMonoOn h S) (hhp : h p < 0)
    (ht : ∃ t ∈ S, 0 < h t) :
    ∃ z ∈ S, p < z ∧ h z = 0 ∧ (∀ x ∈ S, x < z → h x < 0) ∧ (∀ x ∈ S, z < x → 0 < h x) := by
  obtain ⟨t, htS, ht0⟩ := ht
  have hpt : p ≤ t := by
    by_contra hlt
    push Not at hlt
    have := hm htS hp hlt
    linarith
  have hsub : Icc p t ⊆ S := hS.out hp htS
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hpt (hc.mono hsub) ⟨hhp, ht0⟩
  have hzS : z ∈ S := hsub (Ioo_subset_Icc_self hz)
  refine ⟨z, hzS, hz.1, hz0, fun x hx hxz => ?_, fun x hx hzx => ?_⟩
  · rw [← hz0]; exact hm hx hzS hxz
  · rw [← hz0]; exact hm hzS hx hzx

/-- The inductive step of the zero count: if `f' = (a/b) g` with `a < 0 < b`, `f 0 = 1`, and at
the positive zeros of `g` the value `f = (x/b) g'` (from the differential equation), then the
sign-pattern data for `g` with `k` zeros yields the data for `f` with `k + 1` zeros. -/
theorem kumZ_step {f g g' : ℝ → ℝ} {a b : ℝ} {k : ℕ} (hab : a / b < 0) (hb : k = 0 ∨ 0 < b)
    (hf0 : f 0 = 1) (hfd : ∀ x, HasDerivAt f (a / b * g x) x)
    (hode : ∀ x, 0 < x → g x = 0 → f x = x / b * g' x)
    (hQ : kumZ_Q g g' k) : kumZ_Q f (fun x => a / b * g x) (k + 1) := by
  obtain ⟨y, hy0, hymono, hyz, hysign, hylast, X, hX⟩ := hQ
  set c : ℝ := -(a / b) with hcdef
  have hc : 0 < c := by rw [hcdef]; exact neg_pos.mpr hab
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hfd x).continuousAt
  have hdh (j : ℕ) (x : ℝ) :
      HasDerivAt (fun x => (-1 : ℝ) ^ (j + 1) * f x) (c * ((-1) ^ j * g x)) x := by
    have := (hfd x).const_mul ((-1 : ℝ) ^ (j + 1))
    convert this using 1
    rw [hcdef, pow_succ]; ring
  have hmonoy : StrictMonoOn y (Iic k) := strictMonoOn_Iic_of_lt_succ fun j hj => hymono j hj
  have hypos : ∀ j, 1 ≤ j → j ≤ k → 0 < y j := by
    intro j hj1 hjk
    have := hmonoy (show 0 ∈ Iic k from Nat.zero_le k) (show j ∈ Iic k from hjk) (by omega)
    rwa [hy0] at this
  have hfy : ∀ j ≤ k, 0 < (-1) ^ j * f (y j) := by
    intro j hjk
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hy0, hf0]
    · obtain ⟨hz, hd⟩ := hyz j hj hjk
      have hb0 : 0 < b := hb.resolve_left (by omega)
      rw [hode (y j) (hypos j hj hjk) hz]
      have := hypos j hj hjk
      have : (-1 : ℝ) ^ j * (y j / b * g' (y j)) = y j / b * ((-1) ^ j * g' (y j)) := by ring
      rw [this]
      positivity
  have hneg_at (j : ℕ) (hjk : j ≤ k) : (-1 : ℝ) ^ (j + 1) * f (y j) < 0 := by
    have := hfy j hjk
    rw [pow_succ]; linarith
  -- growth beyond the last zero of `g`
  set X1 : ℝ := max X (y k) with hX1
  set hk : ℝ → ℝ := fun x => (-1 : ℝ) ^ (k + 1) * f x with hhk
  have hgrow : ∀ x, X1 + |hk X1| / c + 1 / c ≤ x → 1 ≤ hk x := by
    intro x hx
    have hD := (convex_Ici X1).mul_sub_le_image_sub_of_le_deriv (f := hk)
      (continuous_const.mul hfc).continuousOn
      (fun x _ => (hdh k x).differentiableAt.differentiableWithinAt) (C := c)
      (fun x hx => by
        rw [interior_Ici] at hx
        rw [(hdh k x).deriv]
        have := hX x (le_trans (le_max_left _ _) hx.le)
        nlinarith)
    have hX1x : X1 ≤ x := by
      have : 0 ≤ |hk X1| / c + 1 / c := by positivity
      linarith
    have := hD X1 (mem_Ici.mpr le_rfl) x hX1x hX1x
    have h2 : c * (|hk X1| / c + 1 / c) ≤ c * (x - X1) := by
      gcongr; linarith
    have h3 : c * (|hk X1| / c + 1 / c) = |hk X1| + 1 := by field_simp
    have h4 := neg_abs_le (hk X1)
    linarith
  have hall : ∀ j, ∃ w, j ≤ k → (y j < w ∧ (j < k → w < y (j + 1)) ∧ f w = 0 ∧
      0 < (-1) ^ j * g w ∧
      (∀ x, y j ≤ x → x < w → (-1) ^ (j + 1) * f x < 0) ∧
      (∀ x, w < x → (j < k → x ≤ y (j + 1)) → 0 < (-1) ^ (j + 1) * f x)) := by
    intro j
    by_cases hjk : j ≤ k
    swap
    · exact ⟨0, fun h => absurd h hjk⟩
    have hne : (-1 : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    rcases hjk.lt_or_eq with hlt | heq
    · -- an interior interval `[y j, y (j+1)]`
      have hm : StrictMonoOn (fun x => (-1 : ℝ) ^ (j + 1) * f x) (Icc (y j) (y (j + 1))) :=
        strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop) fun x hx => by
          rw [interior_Icc] at hx
          rw [(hdh j x).deriv]
          exact mul_pos hc (hysign j hlt x hx)
      obtain ⟨z, hzS, hyz', hz0, hlo, hhi⟩ := kumZ_unique_zero (S := Icc (y j) (y (j + 1)))
        ordConnected_Icc (left_mem_Icc.mpr (hymono j hlt).le) (by fun_prop) hm
        (hneg_at j hjk) ⟨y (j + 1), right_mem_Icc.mpr (hymono j hlt).le, hfy (j + 1) hlt⟩
      have hfz : f z = 0 := (mul_eq_zero.mp hz0).resolve_left hne
      have hzlt : z < y (j + 1) := by
        rcases hzS.2.lt_or_eq with h | h
        · exact h
        · exfalso
          have := hfy (j + 1) hlt
          rw [← h, hfz, mul_zero] at this
          exact lt_irrefl _ this
      refine ⟨z, fun _ => ⟨hyz', fun _ => hzlt, hfz, hysign j hlt z ⟨hyz', hzlt⟩,
        fun x hx1 hx2 => hlo x ⟨hx1, hx2.le.trans hzS.2⟩ hx2,
        fun x hx1 hx2 => hhi x ⟨hyz'.le.trans hx1.le, hx2 hlt⟩ hx1⟩⟩
    · -- the last interval `[y k, ∞)`
      subst heq
      have hm : StrictMonoOn (fun x => (-1 : ℝ) ^ (j + 1) * f x) (Ici (y j)) :=
        strictMonoOn_of_deriv_pos (convex_Ici _) (by fun_prop) fun x hx => by
          rw [interior_Ici] at hx
          rw [(hdh j x).deriv]
          exact mul_pos hc (hylast x hx)
      set T : ℝ := X1 + |hk X1| / c + 1 / c with hT
      have hTy : y j ≤ T := by
        have : 0 ≤ |hk X1| / c + 1 / c := by positivity
        have : y j ≤ X1 := le_max_right _ _
        linarith
      obtain ⟨z, hzS, hyz', hz0, hlo, hhi⟩ := kumZ_unique_zero (S := Ici (y j))
        ordConnected_Ici (mem_Ici.mpr le_rfl) (by fun_prop) hm (hneg_at j le_rfl)
        ⟨T, hTy, by have := hgrow T le_rfl; simp only [hhk] at this; linarith⟩
      have hfz : f z = 0 := (mul_eq_zero.mp hz0).resolve_left hne
      refine ⟨z, fun _ => ⟨hyz', fun h => absurd h (lt_irrefl _), hfz, hylast z hyz',
        fun x hx1 hx2 => hlo x hx1 hx2, fun x hx1 _ => hhi x (hyz'.le.trans hx1.le) hx1⟩⟩
  choose w hw using hall
  refine ⟨fun j => if j = 0 then 0 else w (j - 1), by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa [hy0] using (hw 0 (Nat.zero_le k)).1
    · simp only [hj0.ne', ↓reduceIte]
      have h1 := (hw (j - 1) (by omega)).2.1 (by omega)
      rw [show j - 1 + 1 = j by omega] at h1
      exact h1.trans (hw j (by omega)).1
  · intro j hj1 hjk
    simp only [show j ≠ 0 by omega, ↓reduceIte]
    obtain ⟨-, -, hfz, hgs, -, -⟩ := hw (j - 1) (by omega)
    refine ⟨hfz, ?_⟩
    have : (-1 : ℝ) ^ j * (a / b * g (w (j - 1))) = c * ((-1) ^ (j - 1) * g (w (j - 1))) := by
      rw [hcdef, show j = j - 1 + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
    rw [this]
    exact mul_pos hc hgs
  · intro j hj t ht
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at ht
    by_cases hty : y j ≤ t
    · have := (hw j (by omega)).2.2.2.2.1 t hty ht.2
      rw [pow_succ] at this; linarith
    · push Not at hty
      have hj0 : j ≠ 0 := by
        rintro rfl
        simp only [↓reduceIte] at ht
        rw [hy0] at hty
        linarith [ht.1]
      simp only [hj0, ↓reduceIte] at ht
      have := (hw (j - 1) (by omega)).2.2.2.2.2 t ht.1
        (fun _ => by rw [show j - 1 + 1 = j by omega]; exact hty.le)
      rwa [show j - 1 + 1 = j by omega] at this
  · intro t ht
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at ht
    exact (hw k le_rfl).2.2.2.2.2 t ht (fun h => absurd h (lt_irrefl _))
  · exact ⟨_, fun x hx => hgrow x hx⟩

/-- Linear growth: if `h' ≥ c > 0` beyond `X`, then eventually `h ≥ 1`. -/
theorem kumZ_growth {h h' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x) {c X : ℝ} (hc : 0 < c)
    (hX : ∀ x, X ≤ x → c ≤ h' x) : ∃ T, ∀ x, T ≤ x → 1 ≤ h x := by
  have hcont : Continuous h := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  refine ⟨X + |h X| / c + 1 / c, fun x hx => ?_⟩
  have hD := (convex_Ici X).mul_sub_le_image_sub_of_le_deriv (f := h) hcont.continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (C := c)
    (fun x hx => by
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hX x hx.le)
  have hXx : X ≤ x := by
    have : 0 ≤ |h X| / c + 1 / c := by positivity
    linarith
  have := hD X (mem_Ici.mpr le_rfl) x hXx hXx
  have h2 : c * (|h X| / c + 1 / c) ≤ c * (x - X) := by
    gcongr; linarith
  have h3 : c * (|h X| / c + 1 / c) = |h X| + 1 := by field_simp
  have h4 := neg_abs_le (h X)
  linarith

/-- The step `k = 1 ↦ 0` for `a / b < 0` and `b < 0`: the critical point of `f` is a positive
minimum. -/
theorem kumZ_step_down {f g g' : ℝ → ℝ} {a b : ℝ} (hab : a / b < 0) (hb : b < 0)
    (hfd : ∀ x, HasDerivAt f (a / b * g x) x)
    (hode : ∀ x, 0 < x → g x = 0 → f x = x / b * g' x)
    (hQ : kumZ_Q g g' 1) : kumZ_Q f (fun x => a / b * g x) 0 := by
  obtain ⟨y, hy0, hymono, hyz, hysign, hylast, X, hX⟩ := hQ
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hfd x).continuousAt
  have hy1 : 0 < y 1 := by have := hymono 0 (by norm_num); rwa [hy0] at this
  obtain ⟨hg1, hg1'⟩ := hyz 1 le_rfl le_rfl
  have hfy1 : 0 < f (y 1) := by
    rw [hode (y 1) hy1 hg1]
    have : y 1 / b < 0 := div_neg_of_pos_of_neg hy1 hb
    simp only [pow_one, neg_one_mul] at hg1'
    nlinarith
  have hanti : StrictAntiOn f (Icc 0 (y 1)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hfc.continuousOn fun x hx => by
      rw [interior_Icc] at hx
      rw [(hfd x).deriv]
      have := hysign 0 (by norm_num) x (by rwa [hy0])
      simp only [pow_zero, one_mul] at this
      exact mul_neg_of_neg_of_pos hab this
  have hmono : StrictMonoOn f (Ici (y 1)) :=
    strictMonoOn_of_deriv_pos (convex_Ici _) hfc.continuousOn fun x hx => by
      rw [interior_Ici] at hx
      rw [(hfd x).deriv]
      have := hylast x hx
      simp only [pow_one, neg_one_mul] at this
      nlinarith
  refine ⟨fun j => j, by simp, fun j hj => absurd hj (Nat.not_lt_zero _),
    fun j hj1 hj => by omega, fun j hj => absurd hj (Nat.not_lt_zero _), fun x hx => ?_, ?_⟩
  · simp only [pow_zero, one_mul]
    simp only [CharP.cast_eq_zero] at hx
    rcases le_or_gt x (y 1) with h | h
    · rcases h.lt_or_eq with h | h
      · exact hfy1.trans (hanti ⟨hx.le, h.le⟩ ⟨hy1.le, le_rfl⟩ h)
      · rw [h]; exact hfy1
    · exact hfy1.trans (hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr h.le) h)
  · obtain ⟨T, hT⟩ := kumZ_growth hfd (c := -(a / b)) (X := X) (by linarith) fun x hx => by
      have := hX x hx
      simp only [pow_one, neg_one_mul] at this
      nlinarith
    exact ⟨T, fun x hx => by simpa using hT x hx⟩

/-- The step `k ↦ k` for `a / b > 0` and `b < 0`. -/
theorem kumZ_step_same {f g g' : ℝ → ℝ} {a b : ℝ} {k : ℕ} (hab : 0 < a / b) (hb : b < 0)
    (hf0 : f 0 = 1) (hfd : ∀ x, HasDerivAt f (a / b * g x) x)
    (hode : ∀ x, 0 < x → g x = 0 → f x = x / b * g' x)
    (hQ : kumZ_Q g g' k) : kumZ_Q f (fun x => a / b * g x) k := by
  obtain ⟨y, hy0, hymono, hyz, hysign, hylast, X, hX⟩ := hQ
  set c : ℝ := a / b with hcdef
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hfd x).continuousAt
  have hdh (j : ℕ) (x : ℝ) :
      HasDerivAt (fun x => (-1 : ℝ) ^ j * f x) (c * ((-1) ^ j * g x)) x := by
    have := (hfd x).const_mul ((-1 : ℝ) ^ j)
    convert this using 1
    ring
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- no zeros: `f` increases from `1`
    have hmono : StrictMonoOn f (Ici 0) :=
      strictMonoOn_of_deriv_pos (convex_Ici _) hfc.continuousOn fun x hx => by
        rw [interior_Ici] at hx
        rw [(hfd x).deriv]
        have := hylast x (by rwa [hy0])
        simp only [pow_zero, one_mul] at this
        exact mul_pos hab this
    refine kumZ_Q_zero fun x hx => ?_
    rcases hx.lt_or_eq with h | h
    · rw [← hf0]; exact (hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) h).le
    · rw [← h, hf0]
  have hmonoy : StrictMonoOn y (Iic k) := strictMonoOn_Iic_of_lt_succ fun j hj => hymono j hj
  have hypos : ∀ j, 1 ≤ j → j ≤ k → 0 < y j := by
    intro j hj1 hjk
    have := hmonoy (show 0 ∈ Iic k from Nat.zero_le k) (show j ∈ Iic k from hjk) (by omega)
    rwa [hy0] at this
  have hfy : ∀ j, 1 ≤ j → j ≤ k → (-1) ^ j * f (y j) < 0 := by
    intro j hj hjk
    obtain ⟨hz, hd⟩ := hyz j hj hjk
    rw [hode (y j) (hypos j hj hjk) hz]
    have : y j / b < 0 := div_neg_of_pos_of_neg (hypos j hj hjk) hb
    have : (-1 : ℝ) ^ j * (y j / b * g' (y j)) = y j / b * ((-1) ^ j * g' (y j)) := by ring
    rw [this]
    exact mul_neg_of_neg_of_pos (by assumption) hd
  -- on `[0, y 1]` the function increases from `1`
  have h0mono : StrictMonoOn f (Icc 0 (y 1)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hfc.continuousOn fun x hx => by
      rw [interior_Icc] at hx
      rw [(hfd x).deriv]
      have := hysign 0 hk x (by rwa [hy0])
      simp only [pow_zero, one_mul] at this
      exact mul_pos hab this
  have hfirst : ∀ x, 0 ≤ x → x ≤ y 1 → 0 < f x := by
    intro x hx0 hx1
    rcases hx0.lt_or_eq with h | h
    · have := h0mono ⟨le_rfl, (hypos 1 le_rfl hk).le⟩ ⟨hx0, hx1⟩ h
      rw [hf0] at this; linarith
    · rw [← h, hf0]; norm_num
  have hall : ∀ j, ∃ w, 1 ≤ j → j ≤ k → (y j < w ∧ (j < k → w < y (j + 1)) ∧ f w = 0 ∧
      0 < (-1) ^ j * g w ∧
      (∀ x, y j ≤ x → x < w → (-1) ^ j * f x < 0) ∧
      (∀ x, w < x → (j < k → x ≤ y (j + 1)) → 0 < (-1) ^ j * f x)) := by
    intro j
    by_cases hjk : 1 ≤ j ∧ j ≤ k
    swap
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hjk⟩
    obtain ⟨hj1, hjk⟩ := hjk
    have hne : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    rcases hjk.lt_or_eq with hlt | heq
    · have hm : StrictMonoOn (fun x => (-1 : ℝ) ^ j * f x) (Icc (y j) (y (j + 1))) :=
        strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop) fun x hx => by
          rw [interior_Icc] at hx
          rw [(hdh j x).deriv]
          exact mul_pos hab (hysign j hlt x hx)
      have hright : 0 < (-1 : ℝ) ^ j * f (y (j + 1)) := by
        have := hfy (j + 1) (by omega) hlt
        rw [pow_succ] at this; linarith
      obtain ⟨z, hzS, hyz', hz0, hlo, hhi⟩ := kumZ_unique_zero (S := Icc (y j) (y (j + 1)))
        ordConnected_Icc (left_mem_Icc.mpr (hymono j hlt).le) (by fun_prop) hm
        (hfy j hj1 hjk) ⟨y (j + 1), right_mem_Icc.mpr (hymono j hlt).le, hright⟩
      have hfz : f z = 0 := (mul_eq_zero.mp hz0).resolve_left hne
      have hzlt : z < y (j + 1) := by
        rcases hzS.2.lt_or_eq with h | h
        · exact h
        · exfalso
          rw [← h, hfz, mul_zero] at hright
          exact lt_irrefl _ hright
      exact ⟨z, fun _ _ => ⟨hyz', fun _ => hzlt, hfz, hysign j hlt z ⟨hyz', hzlt⟩,
        fun x hx1 hx2 => hlo x ⟨hx1, hx2.le.trans hzS.2⟩ hx2,
        fun x hx1 hx2 => hhi x ⟨hyz'.le.trans hx1.le, hx2 hlt⟩ hx1⟩⟩
    · subst heq
      have hm : StrictMonoOn (fun x => (-1 : ℝ) ^ j * f x) (Ici (y j)) :=
        strictMonoOn_of_deriv_pos (convex_Ici _) (by fun_prop) fun x hx => by
          rw [interior_Ici] at hx
          rw [(hdh j x).deriv]
          exact mul_pos hab (hylast x hx)
      obtain ⟨T, hT⟩ := kumZ_growth (hdh j) (c := c) (X := X) hab fun x hx => by
        have := hX x hx
        nlinarith
      obtain ⟨z, hzS, hyz', hz0, hlo, hhi⟩ := kumZ_unique_zero (S := Ici (y j))
        ordConnected_Ici (mem_Ici.mpr le_rfl) (by fun_prop) hm (hfy j hj1 le_rfl)
        ⟨max T (y j), mem_Ici.mpr (le_max_right _ _),
          by have := hT (max T (y j)) (le_max_left _ _); linarith⟩
      have hfz : f z = 0 := (mul_eq_zero.mp hz0).resolve_left hne
      exact ⟨z, fun _ _ => ⟨hyz', fun h => absurd h (lt_irrefl _), hfz, hylast z hyz',
        fun x hx1 hx2 => hlo x hx1 hx2, fun x hx1 _ => hhi x (hyz'.le.trans hx1.le) hx1⟩⟩
  choose w hw using hall
  refine ⟨fun j => if j = 0 then 0 else w j, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [↓reduceIte, zero_add]
      exact (hypos 1 le_rfl hk).trans (hw 1 le_rfl hk).1
    · simp only [hj0.ne', ↓reduceIte]
      exact ((hw j hj0 hj.le).2.1 hj).trans (hw (j + 1) (by omega) hj).1
  · intro j hj1 hjk
    simp only [show j ≠ 0 by omega, ↓reduceIte]
    obtain ⟨-, -, hfz, hgs, -, -⟩ := hw j hj1 hjk
    refine ⟨hfz, ?_⟩
    have : (-1 : ℝ) ^ j * (a / b * g (w j)) = c * ((-1) ^ j * g (w j)) := by
      rw [hcdef]; ring
    rw [this]
    exact mul_pos hab hgs
  · intro j hj t ht
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at ht
    by_cases hty : t ≤ y (j + 1)
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [↓reduceIte] at ht
        simpa using hfirst t ht.1.le (by simpa using hty)
      · simp only [hj0.ne', ↓reduceIte] at ht
        exact (hw j hj0 hj.le).2.2.2.2.2 t ht.1 (fun _ => hty)
    · push Not at hty
      have := (hw (j + 1) (by omega) hj).2.2.2.2.1 t hty.le ht.2
      rw [pow_succ] at this; linarith
  · intro t ht
    simp only [hk.ne', ↓reduceIte] at ht
    exact (hw k hk le_rfl).2.2.2.2.2 t ht (fun h => absurd h (lt_irrefl _))
  · exact kumZ_growth (hdh k) (c := c) (X := X) hab fun x hx => by
      have := hX x hx
      nlinarith

/-- `x ↦ M(a,b,x)` on the real line, as a real function. -/
noncomputable def kumZ_F (a b : ℝ) : ℝ → ℝ := fun x => (kummerM a b x).re

/-- Positive `b` is not a nonpositive integer. -/
theorem kumZ_not_neg_nat {b : ℝ} (hb : 0 < b) : ∀ k : ℕ, (b : ℂ) ≠ -k := by
  intro k hk
  have h := congrArg re hk
  simp only [ofReal_re, neg_re, natCast_re] at h
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `b ∉ -ℕ` implies `b + 1 ∉ -ℕ`. -/
theorem kumZ_succ_not_neg_nat {b : ℝ} (hb : ∀ k : ℕ, (b : ℂ) ≠ -k) :
    ∀ k : ℕ, ((b + 1 : ℝ) : ℂ) ≠ -k := by
  intro k hk
  apply hb (k + 1)
  push_cast at hk ⊢
  linear_combination hk

/-- `M(a,b,x)` is real for real parameters and argument. -/
theorem kumZ_F_real {a b : ℝ} (hb : ∀ k : ℕ, (b : ℂ) ≠ -k) (x : ℝ) :
    kummerM a b x = (kumZ_F a b x : ℂ) :=
  (kummerM_ofReal_hasSum hb x).2

/-- `M(a,b,0) = 1`. -/
theorem kumZ_F_zero (a b : ℝ) : kumZ_F a b 0 = 1 := by simp [kumZ_F, kummerM_zero]

/-- `d/dx M(a,b,x) = (a/b) M(a+1,b+1,x)` on the real line. -/
theorem kumZ_F_hasDerivAt {a b : ℝ} (hb : ∀ k : ℕ, (b : ℂ) ≠ -k) (x : ℝ) :
    HasDerivAt (kumZ_F a b) (a / b * kumZ_F (a + 1) (b + 1) x) x := by
  have h := (hasDerivAt_kummerM_shift (a := (a : ℂ)) hb (x : ℂ)).real_of_complex
  refine h.congr_deriv ?_
  rw [show ((a : ℂ) / b) = ((a / b : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
  simp [kumZ_F]

/-- At a positive zero `x` of `M(a+1,b+1,·)`, Kummer's equation gives
`M(a,b,x) = (x/b) M'(a+1,b+1,x)`. -/
theorem kumZ_F_ode {a b : ℝ} (hb : ∀ k : ℕ, (b : ℂ) ≠ -k) (ha : a ≠ 0) {x : ℝ} (hx : 0 < x)
    (hg : kumZ_F (a + 1) (b + 1) x = 0) :
    kumZ_F a b x = x / b * ((a + 1) / (b + 1) * kumZ_F (a + 1 + 1) (b + 1 + 1) x) := by
  have hb' := hb
  have hb1' := kumZ_succ_not_neg_nat hb
  have hb2' := kumZ_succ_not_neg_nat hb1'
  have hb1 : ∀ k : ℕ, ((b : ℂ) + 1) ≠ -k := by push_cast at hb1'; exact hb1'
  have hb0 : (b : ℂ) ≠ 0 := by simpa using hb' 0
  have hode := kummerM_ode (a := (a : ℂ)) hb' (z := (x : ℂ)) (by exact_mod_cast hx.ne')
  have hd1 : deriv (kummerM (a : ℂ) b) = fun z => a / b * kummerM (a + 1) (b + 1) z :=
    funext fun z => deriv_kummerM hb' hb0
  have hd2 : iteratedDeriv 2 (kummerM (a : ℂ) b) x =
      a / b * ((a + 1) / (b + 1) * kummerM (a + 1 + 1) (b + 1 + 1) x) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd1]
    exact (((hasDerivAt_kummerM_shift (a := (a : ℂ) + 1) hb1 (x : ℂ)).const_mul
      ((a : ℂ) / b))).deriv
  have hG : kummerM ((a : ℂ) + 1) ((b : ℂ) + 1) x = 0 := by
    have := kumZ_F_real (a := a + 1) (b := b + 1) hb1' x
    push_cast at this
    rw [this, hg, ofReal_zero]
  rw [hd2, hd1] at hode
  simp only [hG, mul_zero, add_zero] at hode
  have hM : kummerM (a : ℂ) b x =
      x / b * ((a + 1) / (b + 1) * kummerM (a + 1 + 1) (b + 1 + 1) x) := by
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    apply mul_left_cancel₀ ha'
    linear_combination -hode
  have := congrArg re hM
  rw [kumZ_F_real hb x, ofReal_re] at this
  rw [this]
  have hr := kumZ_F_real (a := a + 1 + 1) (b := b + 1 + 1) hb2' x
  push_cast at hr
  rw [hr, show (x : ℂ) / b * (((a : ℂ) + 1) / (b + 1) * (kumZ_F (a + 1 + 1) (b + 1 + 1) x : ℂ)) =
    ((x / b * ((a + 1) / (b + 1) * kumZ_F (a + 1 + 1) (b + 1 + 1) x) : ℝ) : ℂ) by push_cast; ring,
    ofReal_re]

/-- For `a ≥ 0 < b`, `M(a,b,x) ≥ 1` on `[0, ∞)`. -/
theorem kumZ_F_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ kumZ_F a b x := by
  obtain ⟨hr, -⟩ := kummerM_ofReal_hasSum (a := a) (kumZ_not_neg_nat hb) x
  have hnonneg : ∀ n : ℕ, 0 ≤ (ascPochhammer ℝ n).eval a /
      ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n := fun n => mul_nonneg
    (div_nonneg (poch_eval_nonneg ha n)
      (mul_nonneg (poch_eval_nonneg hb.le n) (Nat.cast_nonneg _))) (pow_nonneg hx n)
  have hle := hr.summable.sum_le_tsum ({0} : Finset ℕ) (fun n _ => hnonneg n)
  rw [Finset.sum_singleton, hr.tsum_eq] at hle
  simpa [kumZ_F] using hle

/-- The sign-pattern data for `M(a,b,·)` with `⌈-a⌉ = n` zeros. -/
theorem kumZ_F_Q (n : ℕ) : ∀ a b : ℝ, 0 < b → -(n : ℝ) ≤ a → a < -(n : ℝ) + 1 →
    kumZ_Q (kumZ_F a b) (fun x => a / b * kumZ_F (a + 1) (b + 1) x) n := by
  induction n with
  | zero =>
    intro a b hb ha _
    exact kumZ_Q_zero fun x hx => kumZ_F_one_le (by simpa using ha) hb hx
  | succ n ih =>
    intro a b hb ha1 ha2
    push_cast at ha1 ha2
    have ha : a < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact kumZ_step (div_neg_of_neg_of_pos ha hb) (Or.inr hb) (kumZ_F_zero a b)
      (kumZ_F_hasDerivAt (kumZ_not_neg_nat hb))
      (fun x hx hg => kumZ_F_ode (kumZ_not_neg_nat hb) ha.ne hx hg)
      (ih (a + 1) (b + 1) (by linarith) (by linarith) (by linarith))

/-- A real number strictly between consecutive nonpositive integers is not in `-ℕ`. -/
theorem kumZ_not_neg_nat_of_Ioo {b : ℝ} {n : ℕ} (h1 : -((n : ℝ) + 1) < b) (h2 : b < -(n : ℝ)) :
    ∀ k : ℕ, (b : ℂ) ≠ -k := by
  intro k hk
  have hb : b = -(k : ℝ) := by
    have := congrArg re hk; simpa using this
  rw [hb] at h1 h2
  have h3 : (n : ℝ) < k := by linarith
  have h4 : (k : ℝ) < n + 1 := by linarith
  have h3' : n < k := by exact_mod_cast h3
  have h4' : k < n + 1 := by exact_mod_cast h4
  omega

/-- Sign-pattern data for `a > 0` and `b ∈ (-(n+1), -n)`: one zero when `n` is even, none when
`n` is odd. -/
theorem kumZ_F_Q_negb (n : ℕ) : ∀ a b : ℝ, 0 < a → -((n : ℝ) + 1) < b → b < -(n : ℝ) →
    kumZ_Q (kumZ_F a b) (fun x => a / b * kumZ_F (a + 1) (b + 1) x) ((n + 1) % 2) := by
  induction n with
  | zero =>
    intro a b ha hb1 hb2
    simp only [CharP.cast_eq_zero, zero_add, neg_zero] at hb1 hb2
    have hbn := kumZ_not_neg_nat_of_Ioo (n := 0) (by simpa using hb1) (by simpa using hb2)
    have hg : kumZ_Q (kumZ_F (a + 1) (b + 1))
        (fun x => (a + 1) / (b + 1) * kumZ_F (a + 1 + 1) (b + 1 + 1) x) 0 :=
      kumZ_Q_zero fun x hx => kumZ_F_one_le (by linarith) (by linarith) hx
    exact kumZ_step (div_neg_of_pos_of_neg ha hb2) (Or.inl rfl) (kumZ_F_zero a b)
      (kumZ_F_hasDerivAt hbn) (fun x hx hg0 => kumZ_F_ode hbn ha.ne' hx hg0) hg
  | succ n ih =>
    intro a b ha hb1 hb2
    push_cast at hb1 hb2
    have hbn := kumZ_not_neg_nat_of_Ioo (n := n + 1) (by push_cast; linarith)
      (by push_cast; linarith)
    have hab : a / b < 0 := div_neg_of_pos_of_neg ha (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    have hg := ih (a + 1) (b + 1) (by linarith) (by linarith) (by linarith)
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h
    · rw [h] at hg
      have := kumZ_step hab (Or.inl rfl) (kumZ_F_zero a b) (kumZ_F_hasDerivAt hbn)
        (fun x hx hg0 => kumZ_F_ode hbn ha.ne' hx hg0) hg
      rwa [show (n + 1 + 1) % 2 = 0 + 1 by omega]
    · rw [h] at hg
      have := kumZ_step_down hab (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
        (kumZ_F_hasDerivAt hbn) (fun x hx hg0 => kumZ_F_ode hbn ha.ne' hx hg0) hg
      rwa [show (n + 1 + 1) % 2 = 0 by omega]

/-- For noninteger `b < 0`, `b` lies strictly between `-⌈-b⌉` and `-⌈-b⌉ + 1`. -/
theorem kumZ_ceil_bounds {b : ℝ} (hb : b < 0) (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    1 ≤ ⌈-b⌉ ∧ -((⌈-b⌉.toNat : ℕ) : ℝ) < b ∧ b < -((⌈-b⌉.toNat : ℕ) : ℝ) + 1 := by
  have hc1 : 1 ≤ ⌈-b⌉ := by
    rw [Int.one_le_ceil_iff]; linarith
  have hn : (((⌈-b⌉.toNat : ℕ) : ℤ) : ℝ) = (⌈-b⌉ : ℝ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at hn
  refine ⟨hc1, ?_, ?_⟩
  · rw [hn]
    rcases (Int.le_ceil (-b)).lt_or_eq with h | h
    · linarith
    · exfalso
      apply hbi (⌈-b⌉.toNat)
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), ← h]; ring
  · rw [hn]; linarith [Int.ceil_lt_add_one (-b)]

/-- Positive zeros of `M(a,b,·)` are the positive zeros of the real function `kumZ_F a b`. -/
theorem kumZ_posZeros_eq {a b : ℝ} (hb : ∀ k : ℕ, (b : ℂ) ≠ -k) :
    kummerMPosZeros a b = {x : ℝ | 0 < x ∧ kumZ_F a b x = 0} := by
  ext x
  simp only [kummerMPosZeros, mem_ofPred_eq, kumZ_F_real hb x, ofReal_eq_zero]

/-- Real-to-complex transfer of `b ∉ -ℕ`. -/
theorem kumZ_not_neg_nat_real {b : ℝ} (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) : ∀ k : ℕ, (b : ℂ) ≠ -k :=
  fun k hk => hbi k (by exact_mod_cast hk)

/-- Sign-pattern data for `a < -m` and `b ∈ (-(m+1), -m)`: `⌈-a⌉ - (m+1)` zeros. -/
theorem kumZ_F_Q_both (m : ℕ) : ∀ a b : ℝ, -((m : ℝ) + 1) < b → b < -(m : ℝ) → a < -(m : ℝ) →
    kumZ_Q (kumZ_F a b) (fun x => a / b * kumZ_F (a + 1) (b + 1) x)
      (⌈-a⌉.toNat - (m + 1)) := by
  induction m with
  | zero =>
    intro a b hb1 hb2 ha
    simp only [CharP.cast_eq_zero, zero_add, neg_zero] at hb1 hb2 ha
    have hbn := kumZ_not_neg_nat_of_Ioo (n := 0) (by simpa using hb1) (by simpa using hb2)
    have hc : 1 ≤ ⌈-a⌉ := by rw [Int.one_le_ceil_iff]; linarith
    have hn : (((⌈-a⌉.toNat - 1 : ℕ) : ℤ) : ℝ) = (⌈-a⌉ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [Int.cast_natCast] at hn
    have hg := kumZ_F_Q (⌈-a⌉.toNat - 1) (a + 1) (b + 1) (by linarith)
      (by rw [hn]; linarith [Int.le_ceil (-a)]) (by rw [hn]; linarith [Int.ceil_lt_add_one (-a)])
    exact kumZ_step_same (div_pos_of_neg_of_neg ha hb2) hb2 (kumZ_F_zero a b)
      (kumZ_F_hasDerivAt hbn) (fun x hx hg0 => kumZ_F_ode hbn ha.ne hx hg0) hg
  | succ m ih =>
    intro a b hb1 hb2 ha
    push_cast at hb1 hb2 ha
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hbn := kumZ_not_neg_nat_of_Ioo (b := b) (n := m + 1) (by push_cast; linarith)
      (by push_cast; linarith)
    have ha0 : a < 0 := by linarith
    have hb0 : b < 0 := by linarith
    have hg := ih (a + 1) (b + 1) (by linarith) (by linarith) (by linarith)
    have hceil : ⌈-(a + 1)⌉ = ⌈-a⌉ - 1 := by
      rw [show -(a + 1) = -a - 1 by ring, Int.ceil_sub_one]
    rw [hceil, show (⌈-a⌉ - 1).toNat - (m + 1) = ⌈-a⌉.toNat - (m + 1 + 1) by omega] at hg
    exact kumZ_step_same (div_pos_of_neg_of_neg ha0 hb0) hb0
      (kumZ_F_zero a b) (kumZ_F_hasDerivAt hbn)
      (fun x hx hg0 => kumZ_F_ode hbn ha0.ne hx hg0) hg

/-- Sign-pattern data for noninteger `a ∈ (-(p+1), -p)` and noninteger `b` with
`⌈-b⌉ > p + 1`: `(⌈-b⌉ - (p+1)) mod 2` zeros. -/
theorem kumZ_F_Q_swap (p : ℕ) : ∀ a b : ℝ, -((p : ℝ) + 1) < a → a < -(p : ℝ) →
    (∀ k : ℕ, b ≠ -(k : ℝ)) → (p : ℤ) + 1 < ⌈-b⌉ →
    kumZ_Q (kumZ_F a b) (fun x => a / b * kumZ_F (a + 1) (b + 1) x)
      ((⌈-b⌉ - (p + 1)) % 2).toNat := by
  induction p with
  | zero =>
    intro a b ha1 ha2 hbi hcb
    simp only [CharP.cast_eq_zero, zero_add, neg_zero] at ha1 ha2 hcb
    have hb : b < -1 := by
      have := Int.lt_ceil.mp hcb
      push_cast at this; linarith
    obtain ⟨-, hl, hr⟩ := kumZ_ceil_bounds (by linarith) hbi
    obtain ⟨n, hn⟩ : ∃ n, ⌈-b⌉.toNat = n + 1 + 1 := ⟨⌈-b⌉.toNat - 2, by omega⟩
    rw [hn] at hl hr
    push_cast at hl hr
    have hbn := kumZ_not_neg_nat_real hbi
    have hg := kumZ_F_Q_negb n (a + 1) (b + 1) (by linarith) (by linarith) (by linarith)
    have hcount : (n + 1) % 2 = ((⌈-b⌉ - (0 + 1)) % 2).toNat := by omega
    rw [hcount] at hg
    exact kumZ_step_same (div_pos_of_neg_of_neg ha2 (by linarith)) (by linarith)
      (kumZ_F_zero a b) (kumZ_F_hasDerivAt hbn)
      (fun x hx hg0 => kumZ_F_ode hbn ha2.ne hx hg0) hg
  | succ p ih =>
    intro a b ha1 ha2 hbi hcb
    push_cast at ha1 ha2 hcb
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hb : b < 0 := by
      have := Int.lt_ceil.mp (show (0 : ℤ) < ⌈-b⌉ by omega)
      push_cast at this; linarith
    have hbn := kumZ_not_neg_nat_real hbi
    have hbi1 : ∀ k : ℕ, b + 1 ≠ -(k : ℝ) := by
      intro k hk; apply hbi (k + 1); push_cast; linarith
    have hceil : ⌈-(b + 1)⌉ = ⌈-b⌉ - 1 := by
      rw [show -(b + 1) = -b - 1 by ring, Int.ceil_sub_one]
    have hg := ih (a + 1) (b + 1) (by linarith) (by linarith) hbi1 (by rw [hceil]; omega)
    rw [hceil, show ⌈-b⌉ - 1 - ((p : ℤ) + 1) = ⌈-b⌉ - ((p : ℤ) + 1 + 1) by ring] at hg
    have ha0 : a < 0 := by linarith
    exact kumZ_step_same (div_pos_of_neg_of_neg ha0 hb) hb
      (kumZ_F_zero a b) (kumZ_F_hasDerivAt hbn)
      (fun x hx hg0 => kumZ_F_ode hbn ha0.ne hx hg0) hg

/- The old 13.9.3–4 statements were false at `a = 0`; 13.9.5 omitted `a,b < 0`. -/
/-- DLMF 13.9.1: `⌈-a⌉` positive zeros for `a < 0 < b`. -/
@[dlmf 13.9.E1]
theorem kummerM_posZeros_neg_a {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    (kummerMPosZeros a b).encard = Int.toNat ⌈-a⌉ := by
  have hc : 0 ≤ ⌈-a⌉ := Int.ceil_nonneg (by linarith)
  have hn : ((Int.toNat ⌈-a⌉ : ℕ) : ℝ) = (⌈-a⌉ : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hc]
  have hQ := kumZ_F_Q (Int.toNat ⌈-a⌉) a b hb
    (by rw [hn]; linarith [Int.le_ceil (-a)])
    (by rw [hn]; linarith [Int.ceil_lt_add_one (-a)])
  have hset : kummerMPosZeros a b = {x : ℝ | 0 < x ∧ kumZ_F a b x = 0} := by
    ext x
    simp only [kummerMPosZeros, mem_ofPred_eq, kumZ_F_real (kumZ_not_neg_nat hb) x, ofReal_eq_zero]
  rw [hset, kumZ_Q_encard hQ]

/-- Identity under the stated parameter and domain assumptions: `(kummerMPosZeros a b).encard =
1`. -/
@[dlmf 13.9.E3]
theorem kummerM_posZeros_one {a b : ℝ} (ha : 0 < a) (hb0 : -1 < b) (hb1 : b < 0) :
    (kummerMPosZeros a b).encard = 1 := by
  have hb' : ∀ k : ℕ, (b : ℂ) ≠ -k := by
    intro k hk
    have h := congrArg re hk
    simp only [ofReal_re, neg_re, natCast_re] at h
    rcases k with _ | k
    · simp at h; linarith
    · push_cast at h; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  let c : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval a /
    ((ascPochhammer ℝ n).eval b * n.factorial)
  let f : ℝ → ℝ := fun x => (kummerM a b x).re
  have hS (x : ℝ) : HasSum (fun n => c n * x ^ n) (f x) := (kummerM_ofReal_hasSum hb' x).1
  have hR (x : ℝ) : kummerM a b x = (f x : ℂ) := (kummerM_ofReal_hasSum hb' x).2
  have hc1 : c 1 = a / b := by simp [c]
  have hcneg : ∀ n : ℕ, 1 ≤ n → c n ≤ 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hden : (ascPochhammer ℝ (m + 1)).eval b < 0 := by
      rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      exact mul_neg_of_neg_of_pos hb1 (ascPochhammer_pos m _ (by linarith))
    have hnum := ascPochhammer_pos (m + 1) a ha
    exact div_nonpos_of_nonneg_of_nonpos hnum.le
      (mul_nonpos_of_nonpos_of_nonneg hden.le (Nat.cast_nonneg _))
  have hkey : ∀ x y : ℝ, 0 ≤ x → x ≤ y → f y - f x ≤ a / b * (y - x) := by
    intro x y hx hxy
    have hd := (hS y).sub (hS x)
    have hneg : ∀ n, 0 ≤ -(c n * y ^ n - c n * x ^ n) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have := hcneg n hn
        have hp : x ^ n ≤ y ^ n := pow_le_pow_left₀ hx hxy n
        nlinarith
    have hle := hd.neg.summable.sum_le_tsum ({1} : Finset ℕ) (fun n _ => hneg n)
    rw [Finset.sum_singleton, hd.neg.tsum_eq, hc1] at hle
    simp only [pow_one] at hle
    linarith
  have hf0 : f 0 = 1 := by simp [f, kummerM_zero]
  have hanti : StrictAntiOn f (Set.Ici 0) := by
    intro x hx y hy hxy
    have h := hkey x y hx hxy.le
    have hab : a / b < 0 := div_neg_of_pos_of_neg ha hb1
    nlinarith
  have hcont : Continuous f := by
    have h := (hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hb').continuousOn
    rw [Metric.eball_top] at h
    exact continuous_re.comp ((continuousOn_univ.mp h).comp continuous_ofReal)
  set x₁ : ℝ := -2 * b / a with hx₁
  have hx₁pos : 0 < x₁ := div_pos (by linarith) ha
  have hfx₁ : f x₁ < 0 := by
    have h := hkey 0 x₁ le_rfl hx₁pos.le
    rw [hf0, sub_zero, hx₁] at h
    have hbne : b ≠ 0 := hb1.ne
    have : a / b * (-2 * b / a) = -2 := by field_simp
    linarith
  obtain ⟨x₀, hx₀, hfx₀⟩ := intermediate_value_Icc' hx₁pos.le hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f x₁) (f 0) by rw [hf0]; exact ⟨hfx₁.le, zero_le_one⟩)
  have hx₀pos : 0 < x₀ := by
    rcases hx₀.1.eq_or_lt with h | h
    · rw [← h, hf0] at hfx₀; norm_num at hfx₀
    · exact h
  have hset : kummerMPosZeros a b = {x₀} := by
    ext x
    simp only [kummerMPosZeros, Set.mem_ofPred_eq, Set.mem_singleton_iff, hR, ofReal_eq_zero]
    constructor
    · rintro ⟨hx, hfx⟩
      exact hanti.injOn hx.le hx₀pos.le (hfx.trans hfx₀.symm)
    · rintro rfl
      exact ⟨hx₀pos, hfx₀⟩
  rw [hset, Set.encard_singleton]

/-- DLMF 13.9.4 (for `a > 0`; at `a = 0` there are no zeros). -/
@[dlmf 13.9.E4]
theorem kummerM_posZeros_b_le_neg_one {a b : ℝ} (ha : 0 < a) (hb : b ≤ -1)
    (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (kummerMPosZeros a b).encard =
      Int.toNat (⌊-(b / 2)⌋ - ⌊-((b + 1) / 2)⌋) := by
  obtain ⟨hc1, hl, hr⟩ := kumZ_ceil_bounds (by linarith) hbi
  set N := ⌈-b⌉.toNat with hN
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [hn] at hl hr
  push_cast at hl hr
  have hbn := kumZ_not_neg_nat_of_Ioo (n := n) (by linarith) (by linarith)
  have hQ := kumZ_F_Q_negb n a b ha (by linarith) (by linarith)
  have hset : kummerMPosZeros a b = {x : ℝ | 0 < x ∧ kumZ_F a b x = 0} := by
    ext x
    simp only [kummerMPosZeros, mem_ofPred_eq, kumZ_F_real hbn x, ofReal_eq_zero]
  rw [hset, kumZ_Q_encard hQ]
  -- the floor formula is the parity of `n + 1`
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' n
  · rw [hq] at hl hr; push_cast at hl hr
    have h1 : ⌊-(b / 2)⌋ = q := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have h2 : ⌊-((b + 1) / 2)⌋ = q - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [h1, h2, hq]
    have : (2 * q + 1) % 2 = 1 := by omega
    rw [this]; simp
  · rw [hq] at hl hr; push_cast at hl hr
    have h1 : ⌊-(b / 2)⌋ = q := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have h2 : ⌊-((b + 1) / 2)⌋ = q := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [h1, h2, hq]
    have : (2 * q + 1 + 1) % 2 = 0 := by omega
    rw [this]; simp

/-- DLMF 13.9.5. The hypothesis `a < 0` is implied by the others. -/
@[dlmf 13.9.E5]
theorem kummerM_posZeros_ceil {a b : ℝ} (ha : a < 0) (hb : b < 0) (h : ⌈-a⌉ ≥ ⌈-b⌉) (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (kummerMPosZeros a b).encard = Int.toNat (⌈-a⌉ - ⌈-b⌉) := by
  obtain ⟨hc1, hl, hr⟩ := kumZ_ceil_bounds hb hbi
  clear ha
  obtain ⟨m, hm⟩ : ∃ m, ⌈-b⌉.toNat = m + 1 := ⟨⌈-b⌉.toNat - 1, by omega⟩
  rw [hm] at hl hr
  push_cast at hl hr
  have ham : a < -(m : ℝ) := by
    have h1 : ((m : ℤ) + 1) ≤ ⌈-a⌉ := by omega
    have h2 : (m : ℝ) < -a := by
      have := Int.lt_ceil.mp (show (m : ℤ) < ⌈-a⌉ by omega)
      exact_mod_cast this
    linarith
  have hQ := kumZ_F_Q_both m a b (by linarith) (by linarith) ham
  rw [kumZ_posZeros_eq (kumZ_not_neg_nat_real hbi), kumZ_Q_encard hQ]
  congr 1
  omega

/-- DLMF 13.9.6, corrected: the number of positive zeros of `M(a, b, ·)` when
`⌈-b⌉ > ⌈-a⌉ > 0`, for `a` not a nonpositive integer.

DLMF states 13.9.6 for all real `a`, but it fails when `a ∈ -ℕ`, where `M(a, b, ·)` is a
polynomial: at `a = -1`, `b = -3/2` one has `M = 1 + 2x/3` with no positive zero, while the
formula gives one (`kummerM_posZeros_ceil_swap_ne`). DLMF erratum; the hypothesis `hai` is
added. -/
@[dlmf 13.9.E6 "special case: a ∉ -ℕ (the printed statement fails for integer a), DLMF erratum"]
theorem kummerM_posZeros_ceil_swap {a b : ℝ} (h : ⌈-b⌉ > ⌈-a⌉) (ha : 0 < ⌈-a⌉)
    (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) (hai : ∀ k : ℕ, a ≠ -(k : ℝ)) :
    (kummerMPosZeros a b).encard = Int.toNat ((⌈-b⌉ - ⌈-a⌉) % 2) := by
  have ha0 : a < 0 := by
    have := Int.lt_ceil.mp ha; push_cast at this; linarith
  obtain ⟨-, hl, hr⟩ := kumZ_ceil_bounds ha0 hai
  obtain ⟨p, hp⟩ : ∃ p, ⌈-a⌉.toNat = p + 1 := ⟨⌈-a⌉.toNat - 1, by omega⟩
  rw [hp] at hl hr
  push_cast at hl hr
  have hQ := kumZ_F_Q_swap p a b (by linarith) (by linarith) hbi (by omega)
  rw [kumZ_posZeros_eq (kumZ_not_neg_nat_real hbi), kumZ_Q_encard hQ]
  congr 2
  omega

/-- DLMF 13.9.6 as printed fails for integer `a`: at `a = -1`, `b = -3/2` one has
`M(-1,-3/2,x) = 1 + 2x/3 > 0`, while the formula gives one zero. -/
theorem kummerM_posZeros_ceil_swap_ne :
    (kummerMPosZeros (-1) (-3 / 2)).encard ≠
      Int.toNat ((⌈-(-3 / 2 : ℝ)⌉ - ⌈-(-1 : ℝ)⌉) % 2) := by
  have hbi : ∀ k : ℕ, (-3 / 2 : ℝ) ≠ -(k : ℝ) := by
    intro k hk
    have h2 : (2 * k : ℝ) = 3 := by linarith
    have h3 : 2 * k = 3 := by exact_mod_cast h2
    omega
  have hbn := kumZ_not_neg_nat_real hbi
  have hg : kumZ_Q (kumZ_F ((-1 : ℝ) + 1) ((-3 / 2 : ℝ) + 1))
      (fun x => ((-1 : ℝ) + 1) / ((-3 / 2 : ℝ) + 1) * kumZ_F ((-1 : ℝ) + 1 + 1) ((-3 / 2 : ℝ) + 1 + 1) x)
      0 :=
    kumZ_Q_zero fun x _ => by
      norm_num [kumZ_F, kummerM_of_zero_param]
  have hQ := kumZ_step_same (a := -1) (b := -3 / 2) (by norm_num) (by norm_num)
    (kumZ_F_zero _ _) (kumZ_F_hasDerivAt hbn)
    (fun x hx hg0 => kumZ_F_ode hbn (by norm_num) hx hg0) hg
  rw [kumZ_posZeros_eq hbn, kumZ_Q_encard hQ]
  have h1 : ⌈-(-3 / 2 : ℝ)⌉ = 2 := by rw [Int.ceil_eq_iff]; norm_num
  have h2 : ⌈-(-1 : ℝ)⌉ = 1 := by rw [Int.ceil_eq_iff]; norm_num
  rw [h1, h2]
  decide

/-- Estimate under the stated parameter and domain assumptions: `{x : ℝ | x < 0 ∧ kummerM a b x =
0}.encard = (kummerMPosZeros (b - a) b).encard`. -/
@[dlmf 13.9.E7]
theorem kummerM_negZeros_eq {a b : ℝ} (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    {x : ℝ | x < 0 ∧ kummerM a b x = 0}.encard =
      (kummerMPosZeros (b - a) b).encard := by
  have hb : ∀ k : ℕ, (b : ℂ) ≠ -k := fun k hk => hbi k (by exact_mod_cast hk)
  have hz (x : ℝ) : kummerM a b x = 0 ↔ kummerM (b - a) b (-x) = 0 := by
    rw [kummerM_kummer_transform hb, mul_eq_zero]
    simp [Complex.exp_ne_zero]
  have heq : {x : ℝ | x < 0 ∧ kummerM a b x = 0} =
      (fun x : ℝ => -x) ⁻¹' kummerMPosZeros (b - a) b := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, kummerMPosZeros, neg_pos, hz, ofReal_sub, ofReal_neg]
  rw [heq]
  exact Set.encard_preimage_of_bijective (Equiv.neg ℝ).bijective _

end DLMF.Confluent
end
end
