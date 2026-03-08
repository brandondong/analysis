import Mathlib.Tactic
import Analysis.Section_5_4
import Analysis.Section_4_4


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds). Here we use the {name}`upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw [Real.upperBound_def]
  simp_rw [Real.mem_Icc]
  constructor <;> intro h
  . specialize h 1 (by norm_num)
    exact h
  . intro x hx
    linarith

/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M : Real, M ∈ upperBounds (.Ioi 0) := by
  simp_rw [Real.upperBound_def, Real.Ioi_def]
  push_neg
  intro M
  use |M|+1
  constructor
  . simp
    have := abs_nonneg M
    linarith
  . have : |M| ≥ M := by exact le_abs_self M
    linarith

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M
  rw [Real.upperBound_def]
  simp

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
  rw [Real.upperBound_def] at hb ⊢
  intro x hx
  specialize hb x hx
  linarith

/-- Definition 5.5.5 (least upper bound).  Here we use the {name}`IsLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1 : Real) := by
  rw [Real.isLUB_def]
  constructor
  . simp [Real.upperBound_def]
  simp_rw [Real.upperBound_def]
  intro M
  intro h
  specialize h 1 (by simp)
  exact h

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  simp_rw [Real.isLUB_def]
  push_neg
  intro M hM
  use M-1
  constructor
  . simp
  . linarith

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by
  grind [Real.isLUB_def]

/-- Definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
  set r: Real := ↑(1 / ((n:ℚ) + 1))
  -- Contrapositive: Assume there is no switch point -> prove K is not an upper bound.
  contrapose! hK
  -- We can use induction from L up to K to show that these are all not upper bounds.
  rw [lt_iff_exists_pos_add] at hLK
  obtain ⟨ c, hc, rfl ⟩ := hLK
  obtain ⟨ c, rfl ⟩ := Int.eq_succ_of_zero_lt hc
  clear hc
  suffices h (c': ℕ) (hc': c' ≤ c+1) : ↑(L + (↑c')) * r ∉ upperBounds E
  . specialize h (c+1) (by omega)
    exact h
  induction' c' with c' IH
  . simp [hL]
  contrapose! hK
  use L + ↑(c' + 1), (by omega), (by omega), hK
  specialize IH (by omega)
  suffices h : ((L + ↑(c' + 1)):ℤ) - (1:Real) = ((L + ↑c'):ℤ)
  . rw [h]
    exact IH
  simp
  linarith

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by
  set r: ℚ := ((n:ℚ) + 1)
  -- Assume to the contrary that m != m'.
  by_contra hne
  -- Wlog: m < m', then (m'-1)/r must be an upper bound.
  wlog h : m < m' generalizing m m'
  . exact this hm'1 hm'2 hm1 hm2 (by omega) (by omega)
  contrapose! hm'2; clear hm'2 hne hm'1 hm2
  rw [upperBound_def] at *
  intro x hx
  specialize hm1 x hx
  replace h : m ≤ m'-1 := by omega
  have hr : r > 0
  . unfold r
    linarith
  have hm : ↑m≤ (↑m' - 1:ℚ) := by norm_cast
  calc
    x ≤ ((↑m / r):ℚ) := hm1
    _ ≤ (((m'-1) / r):ℚ) := by {
      suffices h : (↑m / r) ≤ ↑((↑m' - 1) / r)
      . exact GCongr.ratCast_le_ratCast h
      exact (div_le_div_iff_of_pos_right hr).mpr hm
    }
    _ = _ := by {
      suffices h : (((m'-1) / r):ℚ) = (↑m' / r - 1 / r)
      . rw [h]
      exact sub_div (↑m') 1 r
    }

/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at *
  unfold Section_4_3.dist at *
  -- If a j and a k are the same positivity, then absolute value does nothing.
  -- Otherwise, they get even closer.
  intro e he
  specialize ha e he
  obtain ⟨ N, hN ⟩ := ha
  use N
  intro j hj k hk
  specialize hN j hj k hk
  rw [abs_le] at hN ⊢
  simp
  obtain h1 | h1 := lt_or_ge (a k) 0
  . rw [abs_of_neg h1]
    obtain h2 | h2 := lt_or_ge (a j) 0
    . rw [abs_of_neg h2]
      constructor <;> linarith
    . rw [abs_of_nonneg h2]
      constructor <;> linarith
  . rw [abs_of_nonneg h1]
    obtain h2 | h2 := lt_or_ge (a j) 0
    . rw [abs_of_neg h2]
      constructor <;> linarith
    . rw [abs_of_nonneg h2]
      constructor <;> linarith

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
  rw [Real.LIM_eq_LIM ha hb, Sequence.equiv_iff] at h
  have ha' := Sequence.IsCauchy.abs ha
  have hb' := Sequence.IsCauchy.abs hb
  rw [Real.LIM_eq_LIM ha' hb', Sequence.equiv_iff]
  -- Same as above...
  intro e he
  specialize h e he
  obtain ⟨ N, hN ⟩ := h
  use N
  intro n hn
  specialize hN n hn
  rw [abs_le] at hN ⊢
  simp
  obtain h1 | h1 := lt_or_ge (a n) 0
  . rw [_root_.abs_of_neg h1]
    obtain h2 | h2 := lt_or_ge (b n) 0
    . rw [_root_.abs_of_neg h2]
      constructor <;> linarith
    . rw [_root_.abs_of_nonneg h2]
      constructor <;> linarith
  . rw [_root_.abs_of_nonneg h1]
    obtain h2 | h2 := lt_or_ge (b n) 0
    . rw [_root_.abs_of_neg h2]
      constructor <;> linarith
    . rw [_root_.abs_of_nonneg h2]
      constructor <;> linarith

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
    LIM a = LIM |a| := by
  rw [gt_iff, isPos_def] at h
  obtain ⟨ a', ha'b, ha', h ⟩ := h
  simp only [sub_zero] at h
  rw [boundedAwayPos_def] at ha'b
  obtain ⟨ c, hc, ha'b ⟩ := ha'b
  -- Need to prove a is arbitrarily close to |a| after a certain point.
  -- We know a is arbitrarily close to a' which is >= c so we can find a point where a is non-negative.
  rw [Real.LIM_eq_LIM ha ha', Sequence.equiv_iff] at h
  rw [Real.LIM_eq_LIM ha (Sequence.IsCauchy.abs ha), Sequence.equiv_iff]
  specialize h c hc
  obtain ⟨ N, hN ⟩ := h
  intro _ _
  use N
  intro n hn
  specialize hN n hn
  specialize ha'b n
  simp
  have goal : a n ≥ 0
  . rw [abs_le] at hN
    linarith
  rw [abs_of_nonneg goal]
  simp
  linarith

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  obtain h | h | h := lt_trichotomy (LIM a) 0
  . rw [_root_.abs_of_neg h]
    set b := -a
    have hb2 : LIM b > 0
    . unfold b
      rw [gt_iff]
      rw [← gt_iff_lt, gt_iff] at h
      suffices h : (LIM (-a) - 0) = (0 - LIM a)
      . rwa [h]
      simp
      rw [Real.neg_LIM a ha]
    have hb : (b:Sequence).IsCauchy
    . simp [b]
      exact Sequence.IsCauchy.neg a ha
    have := Real.LIM.abs_eq_pos hb2 hb
    calc
      _ = LIM b := by {
        simp [b]
        rw [Real.neg_LIM a ha]
      }
      _ = LIM |b| := this
      _ = _ := by simp [b]
  . simp [h]
    rw [← Real.LIM.zero] at h ⊢
    rw [Real.LIM_eq_LIM ha (Sequence.IsCauchy.const _), Sequence.equiv_iff] at h
    rw [Real.LIM_eq_LIM (Sequence.IsCauchy.const _) (Sequence.IsCauchy.abs ha), Sequence.equiv_iff]
    simp at h ⊢
    exact h
  . have := Real.LIM.abs_eq_pos h ha
    rwa [abs_of_nonneg (by linarith)]

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
    (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by
  -- Should be super similar proof to Real.LIM_of_le except we push chosen n further back.
  obtain ⟨ b, hb, rfl ⟩ := Real.eq_lim x
  -- Assume to the contrary that a > b.
  contrapose! h
  -- Then there exists c such that a' = a - b > c.
  rw [← gt_iff_lt, gt_iff, Real.LIM_sub hcauchy hb, Real.isPos_def] at h
  obtain ⟨ a', ha'b, ha', h ⟩ := h
  rw [boundedAwayPos_def] at ha'b
  obtain ⟨ c, hc, ha'b ⟩ := ha'b
  -- Since a' is equivalent to a - b, find some N where difference is < c/2.
  -- Also some N2 where b changes less than c/2.
  rw [Real.LIM_eq_LIM (by {
    apply Sequence.IsCauchy.sub
    . exact hcauchy
    . exact hb
  }) ha', Sequence.equiv_iff] at h
  specialize h (c/32) (by linarith)
  obtain ⟨ N, hN ⟩ := h
  rw [Sequence.IsCauchy.coe] at hcauchy
  specialize hcauchy (c/32) (by linarith)
  obtain ⟨ N2, hN2 ⟩ := hcauchy
  intro N3
  use N+N2+N3
  use (by omega)
  rw [← gt_iff_lt, gt_iff, Real.isPos_def]
  use SwapFirst (fun n ↦ a (N+N2+N3) - b n) (N+N2+N3) c
  have hc : ((↑fun n ↦ a (N+N2+N3) - b n):Sequence).IsCauchy
  . have : (↑fun n ↦ a (N+N2+N3) - b n) = (↑fun _ ↦ a (N+N2+N3)) - b
    . simp [funext_iff]
    rw [this]
    apply Sequence.IsCauchy.sub
    . exact (Sequence.IsCauchy.const _)
    . exact hb
  split_ands
  . apply SwapFirst_bounded_away_pos
    use (c/32), (by linarith)
    constructor
    . intro n hn
      -- a' is positive and so a n - b n which is arbitrarily close is also positive.
      -- a n is arbitrarily close to a N and so the goal holds.
      specialize hN n (by omega)
      specialize ha'b n
      unfold Section_4_3.dist at hN2
      specialize hN2 n (by omega) (N+N2+N3) (by omega)
      simp [abs_le] at hN2 hN
      linarith
    . linarith
  . apply SwapFirst_cauchy
    exact hc
  . rw [SwapFirst_lim_eq hc, ratCast_def, Real.LIM_sub (Sequence.IsCauchy.const _) hb]
    apply LIM_eq_fun_eq
    simp [funext_iff]

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by
  have hqc : (q:Sequence).IsCauchy
  . rw [Sequence.IsCauchy.coe]
    intro e he
    unfold Section_4_3.dist
    -- Need N such that 1 / (N + 1) <= e.
    -- Equivalently, 1/e-1 <= 1/e <= N
    obtain ⟨ N, hN ⟩ := exists_nat_gt (1/e)
    use N
    intro j hj k hk
    specialize hq N j hj k hk
    have goal : 1 / (N + 1) ≤ e
    . rw [one_div_le]
      . linarith
      . linarith
      . exact he
    linarith
  use hqc
  intro M
  have h : (((fun (x:ℕ) ↦ q M) - q):Sequence).IsCauchy
  . apply Sequence.IsCauchy.sub
    . exact Sequence.IsCauchy.const _
    . exact hqc
  rw [ratCast_def, Real.LIM_sub (Sequence.IsCauchy.const _) hqc, Real.LIM_abs h]
  apply Real.LIM_of_le'
  . apply Sequence.IsCauchy.abs
    exact h
  use M
  intro n hn
  specialize hq M M (by omega) n hn
  simp only [Pi.abs_apply, Pi.sub_apply, Rat.cast_abs, Rat.cast_sub]
  norm_cast
  have : 1 / ((((M:ℕ) + 1):ℕ):Real) = ((1:ℚ) / ((M:ℚ) + (1:ℚ)):ℚ)
  . simp
  rw [this]; clear this
  exact GCongr.ratCast_le_ratCast hq

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hb : (b:Sequence).IsCauchy := .harmonic'
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  . intro x hx; apply LIM_of_ge claim3; intro n
    exact (upperBound_def E (a n)).mp (hm1 n) x hx
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
  rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers {syntax term}`⊤` to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers {syntax term}`⊥` to denote the -∞ element. -/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real)
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  use x; obtain h | h | h := trichotomous' (x^2) 2
  . have claim11: ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 - 4*ε > 2 := by
      set ε := min (1/2) ((x^2-2)/8)
      have hx : x^2 - 2 > 0 := by linarith
      have hε : 0 < ε := by positivity
      observe hε1: ε ≤ 1/2
      observe hε2: ε ≤ (x^2-2)/8
      refine' ⟨ ε, hε, _, _ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim11
    have claim12: (x-ε)^2 > 2 := calc
      _ = x^2 - 2 * ε * x + ε * ε := by ring
      _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
      _ = x^2 - 4 * ε := by ring
      _ > 2 := hε3
    have why (y:Real) (hy: y ∈ E) : x - ε ≥ y
    . by_contra hc
      simp at hc
      have hc2 : (x - ε) ^ 2 < y ^ 2
      . have h1 : x - ε > 0 := by linarith
        have hy : y > 0 := by linarith
        calc
          _ = (x - ε) * (x - ε) := by ring
          _ < y * y := by gcongr
          _ = _ := by ring
      simp [E] at hy
      linarith
    have claim13: x-ε ∈ upperBounds E := by rwa [upperBound_def]
    have claim14: x ≤ x-ε := by grind [isLUB_def]
    linarith
  . have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  assumption

theorem Real.exist_irrational_gt_one : ∃ x:Real, (¬ ∃ q:ℚ, x = (q:Real)) ∧ x > 1 := by
  obtain ⟨ x, hx ⟩ := Real.exist_sqrt_two
  use |x|
  constructor
  . have h := Rat.not_exist_sqrt_two
    contrapose! h
    obtain ⟨ q, hq ⟩ := h
    use q
    -- norm_cast at hx
    have : |x|^2 = x ^ 2 := by exact sq_abs x
    rw [← this, hq] at hx
    norm_cast at hx
  . contrapose! hx
    rw [abs_le] at hx
    suffices h : x ^ 2 <= 1
    . linarith
    simp [abs_le]
    exact hx

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by
  obtain ⟨ x, hx, _ ⟩ := Real.exist_irrational_gt_one
  use x

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by
  simp only [isLUB_def, upperBound_def] at h
  simp only [isGLB_def, lowerBound_def]
  obtain ⟨ h1, h2 ⟩ := h
  constructor
  . intro x hx
    rw [Real.mem_neg] at hx
    specialize h1 (-x) hx
    linarith
  . intro M'
    specialize h2 (-M')
    intro h3
    suffices h4 : (∀ x ∈ E, x ≤ -M')
    . have := h2 h4
      linarith
    intro x hx
    specialize h3 (-x)
    suffices h4 : -x ∈ -E
    . specialize h3 h4
      linarith
    exact Set.neg_mem_neg.mpr hx

theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  have hE': Set.Nonempty (-E) := by exact Set.Nonempty.neg hE
  have hbound': BddAbove (-E)
  . exact BddBelow.neg hbound
  obtain ⟨ M, hM ⟩ := Real.LUB_exist hE' hbound'
  have h := Real.inf_neg hM
  use -M
  simp at h
  exact h

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by
  -- Consider a, b rationals such that x < a < b < y.
  -- Then a + (b-a)/sqrt(2) fits the bounds and is irrational.
  obtain ⟨ b, hb1, hb2 ⟩ := Real.rat_between hxy
  obtain ⟨ a, ha1, ha2 ⟩ := Real.rat_between hb1
  obtain ⟨ i, hi, hi1 ⟩ := Real.exist_irrational_gt_one
  use a + (b-a)/i
  have hba1 : (b:Real) - a > 0 := by linarith
  have hi2' : i > 0 := by linarith
  have hbai : (b-a)/i < b-a
  . have : (↑b - ↑a) / i = (↑b - ↑a) * i⁻¹ := by ring
    rw [this]; clear this
    have : i⁻¹ < 1
    . field_simp
      rw [one_div_lt (by linarith) (by norm_num)]
      simp [hi1]
    calc
      _ < (↑b - ↑a) * (1:Real) := by exact mul_lt_mul_of_pos_left i⁻¹ 1 (↑b - ↑a) this hba1
      _ = _ := by ring
  have hbai2 : (↑b - ↑a) / i > 0
  . exact div_pos hba1 hi2'
  split_ands
  . linarith
  . linarith
  . contrapose! hi
    obtain ⟨ q, hq ⟩ := hi
    use (b-a)/(q-a)
    have hqa : (q:Real) - a ≠ 0 := by linarith
    replace hq : (↑b - ↑a) / i = ↑q - a := by linarith
    have goal : (↑b - ↑a) / (q - a) = i
    . have hi : i ≠ 0 := by linarith
      have : (↑b - ↑a) /i = (↑b - ↑a) * i⁻¹ := by ring
      rw [this] at hq; clear this
      replace hq : (↑b - ↑a) = (↑q - ↑a) * i
      . symm
        rw [← eq_mul_inv_iff_mul_eq₀ hi]
        exact hq.symm
      symm at hq
      rw [← eq_inv_mul_iff_mul_eq₀ hqa] at hq
      rw [hq]
      ring
    rw [← goal]
    simp

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the {name}`sSup` operation to build a conditionally complete lattice structure on {name}`Real`. -/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
