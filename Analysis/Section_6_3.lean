import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

theorem neg_one_pow_bounded (n: ℕ) : (-1) ^ n ≤ (1:EReal) ∧ (-1) ^ n ≥ (-1:EReal) := by
  have : ((-1 : ℝ) : EReal) = -1 := by rfl
  rw [← this]; clear this
  have : ((1 : ℝ) : EReal) = 1 := by rfl
  rw [← this]; clear this
  norm_cast
  induction' n with n IH
  . simp
  rw [pow_succ]
  omega

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  simp [Sequence.sup]
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . intro a ha
    simp at ha
    obtain ⟨ n, hn, rfl ⟩ := ha
    simp [hn]
    lift n to ℕ using hn
    simp
    exact (neg_one_pow_bounded (n+1)).1
  . intro b hb
    use 1
    constructor
    . simp
      use 1, (by norm_num)
      simp
    . exact hb

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  simp [Sequence.inf]
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . intro a ha
    simp at ha
    obtain ⟨ n, hn, rfl ⟩ := ha
    simp [hn]
    lift n to ℕ using hn
    simp
    exact (neg_one_pow_bounded (n+1)).2
  . intro b hb
    use -1
    constructor
    . simp
      use 0, (by norm_num)
      simp
    . exact hb

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  simp [Sequence.sup]
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . intro a ha
    simp at ha
    obtain ⟨ n, hn, rfl ⟩ := ha
    simp [hn]
    lift n to ℕ using hn
    simp
    norm_cast
    field_simp
    simp
  . intro b hb
    use 1
    constructor
    . simp
      use 0, (by norm_num)
      simp
    . exact hb

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  simp [Sequence.inf]
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . intro a ha
    simp at ha
    obtain ⟨ n, hn, rfl ⟩ := ha
    simp [hn]
    lift n to ℕ using hn
    simp
    linarith
  . intro b hb
    obtain h | rfl | rfl := EReal.def b
    . obtain ⟨ b, rfl ⟩ := h
      simp at hb
      obtain ⟨ N, hN ⟩ := exists_nat_gt b⁻¹
      have : b⁻¹ = 1/b := by ring
      have hb2 : 1/b > 0 := one_div_pos.mpr hb
      have hN2 : (0:ℝ) < N := by linarith
      rw [this, one_div_lt hb hN2] at hN; clear this
      use (((1:ℝ) / (N:ℝ)):ℝ)
      constructor
      . simp
        replace hN : 0 < N
        . norm_cast at hN2
        rw [← Nat.exists_add_one_eq] at hN
        obtain ⟨ N, rfl ⟩ := hN
        use N
        constructor
        . simp
        simp
      . norm_cast
    . use 1
      constructor
      . simp
        use 0, (by norm_num)
        simp
      . tauto
    . simp at hb

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  simp [Sequence.sup]
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . intro a _
    simp [EReal.le_iff]
  . intro b hb
    obtain ⟨ b, rfl ⟩ | rfl | rfl := EReal.def b
    . clear hb
      obtain ⟨ N, hN ⟩ := exists_nat_gt b
      use N+1
      simp
      constructor
      . use N
        simp
      . norm_cast
        simp
        linarith
    . simp at hb
    . use 1
      simp
      constructor
      . use 0, (by norm_num)
        simp
      . tauto

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  simp [Sequence.inf]
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . intro a ha
    simp at ha
    obtain ⟨ N, hN, rfl ⟩ := ha
    simp [hN]
    norm_cast
    omega
  . intro b hb
    use 1
    constructor
    . simp
      use 0, (by norm_num)
      simp
    . exact hb

abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  rw [Sequence.isBounded_def]
  unfold Sequence.BoundedBy
  constructor
  . intro ⟨ M, hM, h ⟩
    constructor
    . use M
      intro n hn
      specialize h n
      rw [abs_le] at h
      exact h.2
    . use -M
      intro n hn
      specialize h n
      rw [abs_le] at h
      exact h.1
  . intro ⟨ ⟨ M1, hM1 ⟩, ⟨ M2, hM2 ⟩ ⟩
    use max (|M1|) (|M2|)
    constructor
    . simp
    intro n
    obtain h | h := lt_or_ge n a.m
    . have := a.vanish n h
      simp [this]
    specialize hM1 n h
    specialize hM2 n h
    rw [abs_le]
    constructor
    . have : -max |M1| |M2| = min (-|M1|) (-|M2|) := by exact neg_sup |M1| |M2|
      simp [this]; clear this
      right
      obtain hm | hm := lt_or_ge M2 0
      . rw [abs_of_neg hm]
        simp [hM2]
      . rw [abs_of_nonneg hm]
        linarith
    . simp
      left
      obtain hm | hm := lt_or_ge M1 0
      . rw [abs_of_neg hm]
        linarith
      . rw [abs_of_nonneg hm]
        exact hM1

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by
  rw [Sequence.isBounded_def] at h
  unfold Sequence.BoundedBy at h
  obtain ⟨ M, hM, h ⟩ := h
  unfold EReal.IsFinite
  obtain hy | hy | hy := EReal.def a.sup
  . exact hy
  . simp [Sequence.sup] at hy
    rw [← isLUB_iff_sSup_eq, isLUB_iff_le_iff] at hy
    specialize hy M
    have : ¬ (⊤:EReal) ≤ M := by tauto
    simp [this] at hy
    contrapose! hy
    simp [upperBounds]
    intro _ n _ rfl
    specialize h n
    rw [abs_le] at h
    simp [h.2]
  . simp only [Sequence.sup] at hy
    rw [sSup_eq_bot] at hy
    contrapose! hy
    use a.seq (a.m)
    simp
    use a.m

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
  rw [Sequence.isBounded_def] at h
  unfold Sequence.BoundedBy at h
  obtain ⟨ M, hM, h ⟩ := h
  unfold EReal.IsFinite
  obtain hy | hy | hy := EReal.def a.inf
  . exact hy
  . simp [Sequence.inf] at hy
    rw [← isGLB_iff_sInf_eq, isGLB_iff_le_iff] at hy
    specialize hy ⊤
    simp [lowerBounds] at hy
    specialize hy (a.m) (by omega) (by rfl)
    tauto
  . simp [Sequence.inf] at hy
    rw [sInf_eq_bot] at hy
    specialize hy (-M)
    have : (⊥:EReal) < -↑M := by tauto
    simp [this] at hy; clear this
    contrapose! hy
    intro n _
    specialize h n
    norm_cast
    rw [abs_le] at h
    exact h.1

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by
  simp [Sequence.sup]
  apply le_sSup
  simp
  use n

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by
  simp only [Sequence.sup]
  apply sSup_le
  intro b hb
  simp at hb
  obtain ⟨ n, hn, rfl ⟩ := hb
  exact h n hn

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by
  contrapose! h
  simp only [Sequence.sup]
  apply sSup_le
  intro b hb
  simp at hb
  obtain ⟨ n, hn, rfl ⟩ := hb
  specialize h n hn
  contrapose! h
  use h
  apply le_sSup
  simp
  use n

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by
  simp [Sequence.inf]
  apply sInf_le
  simp
  use n

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
  simp only [Sequence.inf]
  apply le_sInf
  intro b hb
  simp at hb
  obtain ⟨ n, hn, rfl ⟩ := hb
  exact h n hn

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by
  contrapose! h
  simp only [Sequence.inf]
  apply le_sInf
  intro b hb
  simp at hb
  obtain ⟨ n, hn, rfl ⟩ := hb
  specialize h n hn
  contrapose! h
  use h
  apply sInf_le
  simp
  use n

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

theorem Sequence.convergent_of_monotone_helper {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    ∃ y:ℝ, y = a.sup ∧ a.TendsTo y := by
  obtain ⟨ M, hM ⟩ := hbound
  unfold Sequence.BddAboveBy at hM
  -- Since a is bounded from above, a.sup is in the reals and is the limit.
  have h : (∃ y:ℝ, y = a.sup)
  . obtain h | h | h := EReal.def a.sup
    . exact h
    . simp [Sequence.sup] at h
      rw [← isLUB_iff_sSup_eq, isLUB_iff_le_iff] at h
      specialize h M
      contrapose! h
      right
      simp [upperBounds]
      intro _ n hn rfl
      specialize hM n hn
      simp [hM]
    . simp at h
      specialize h (a.seq a.m) a.m (by omega) (by rfl)
      simp at h
  obtain ⟨ y, hy ⟩ := h
  use y, hy
  -- For any e, consider a.sup-e which cannot be an upper bound.
  rw [Sequence.tendsTo_def]
  intro e he
  rw [Real.eventuallyClose_def]
  have : a.sup - e < a.sup
  . rw [← hy]
    norm_cast
    linarith
  obtain ⟨ N, hN, h1, h2 ⟩ := Sequence.exists_between_lt_sup this; clear this
  -- Therefore there exists some a n closer and all n' >= n are closer still due to monoticity.
  use N, hN
  rw [Real.closeSeq_def]
  intro n hn
  rw [Real.dist_eq]
  simp at hn
  simp [hn]
  rw [abs_sub_comm, abs_of_nonneg (by {
    suffices h : a.seq n ≤ a.sup
    . rw [← hy] at h
      simp at h
      linarith
    simp [Sequence.sup]
    apply le_sSup
    simp
    use n, hn.1
  })]
  unfold Sequence.IsMonotone at hmono
  have h3 : a.seq n ≥ a.seq N
  . replace hn := hn.2
    rw [le_iff_exists_nonneg_add] at hn
    obtain ⟨ c, hc, rfl ⟩ := hn
    lift c to ℕ using hc
    induction' c with c IH
    . simp
    specialize hmono (N+c) (by omega)
    have : N + ↑(c + 1) = N + c + 1
    . omega
    rw [this]
    linarith
  have h4 : y - a.seq N ≤ e
  . rw [← hy] at h1
    norm_cast at h1
    linarith
  linarith

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by
  rw [Sequence.convergent_def]
  obtain ⟨ y, _, ha ⟩ := Sequence.convergent_of_monotone_helper hbound hmono
  use y

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by
  obtain ⟨ y, hy, h2 ⟩ := Sequence.convergent_of_monotone_helper hbound hmono
  obtain ⟨ hac, h ⟩ := Sequence.lim_eq.mp h2
  rw [h, hy]

theorem Sequence.neg_bound_helper {a:Sequence} (hbound: a.BddBelow) : ((-1:ℝ) • a).BddAbove := by
  obtain ⟨ M, hM ⟩ := hbound
  use -M
  intro n hn
  simp [Sequence.smul_m] at hn
  specialize hM n hn
  simp [hM]

theorem Sequence.neg_tone_helper {a:Sequence} (hmono: a.IsAntitone) : ((-1:ℝ) • a).IsMonotone := by
  intro n hn
  simp [Sequence.smul_m] at hn
  specialize hmono n hn
  simp [hmono]

theorem Sequence.neg_tendsTo_helper {a:Sequence} {L:ℝ} (hL: ((-1:ℝ) • a).TendsTo L) : a.TendsTo (-L) := by
  rw [Sequence.tendsTo_def] at *
  intro e he
  specialize hL e he
  rw [Real.eventuallyClose_def] at *
  obtain ⟨ N, hN, h ⟩ := hL
  simp [Sequence.smul_m] at hN
  use N, hN
  rw [Real.closeSeq_def] at *
  intro n hn
  specialize h n (by simp [Sequence.smul_m, hn])
  rw [Real.dist_eq] at *
  simp [Sequence.smul_m, hn] at h
  simp [hn]
  have : -a.seq n - L = -(a.seq n + L) := by ring
  rwa [this, abs_neg] at h

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by
  have h : ((-1:ℝ) • a).Convergent
  . apply Sequence.convergent_of_monotone
    . exact Sequence.neg_bound_helper hbound
    . exact Sequence.neg_tone_helper hmono
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := h
  have := Sequence.neg_tendsTo_helper hL
  use -L

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by
  have hbound2 := neg_bound_helper hbound
  have hmono2 := neg_tone_helper hmono
  have h : ∃ y:ℝ, y = ((-1:ℝ) • a).sup ∧ ((-1:ℝ) • a).TendsTo y
  . apply Sequence.convergent_of_monotone_helper
    . exact hbound2
    . exact hmono2
  obtain ⟨ y, hy, hy2 ⟩ := h
  have h : lim ((-1:ℝ) • a) = ((-1:ℝ) • a).sup
  . apply Sequence.lim_of_monotone
    . exact hbound2
    . exact hmono2
  have h1 : lim a = -lim ((-1:ℝ) • a)
  . suffices goal : a.TendsTo (-y)
    . rw [Sequence.lim_eq] at *
      linarith
    exact neg_tendsTo_helper hy2
  have h2 : a.inf = -((-1:ℝ) • a).sup
  . rw [← hy]
    simp [Sequence.sup] at hy
    symm at hy
    rw [← isLUB_iff_sSup_eq, isLUB_iff_le_iff] at hy
    simp [Sequence.inf]
    rw [← isGLB_iff_sInf_eq, isGLB_iff_le_iff]
    intro b
    specialize hy (-b)
    constructor <;> intro h
    . have := hy.mp (by exact EReal.le_neg_of_le_neg h)
      simp [lowerBounds]
      simp [upperBounds] at this
      intro _ n hn rfl
      exact EReal.neg_le_neg_iff.mp (this n hn rfl)
    . have := hy.mpr (by {
        simp [lowerBounds] at h
        simp [upperBounds]
        intro _ n hn rfl
        exact EReal.neg_le_neg_iff.mpr (h n hn rfl)
      })
      exact EReal.le_neg_of_le_neg this
  rw [h1, h2, ← h]
  simp

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by
  constructor <;> intro h
  . exact bounded_of_convergent h
  . apply Sequence.convergent_of_monotone
    . rw [Sequence.bounded_iff] at h
      exact h.1
    . exact ha

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by
  constructor <;> intro h
  . exact bounded_of_convergent h
  . apply Sequence.convergent_of_antitone
    . rw [Sequence.bounded_iff] at h
      exact h.2
    . exact ha

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
theorem example_6_3_9_mono : (Example_6_3_9:Sequence).IsMonotone := by sorry

/-- Example 6.3.9 -/
theorem example_6_3_9_bdd_above_by : (Example_6_3_9:Sequence).BddAboveBy 4 := by sorry

theorem example_6_3_9_bdd_above : (Example_6_3_9:Sequence).BddAbove := by
  use 4
  exact example_6_3_9_bdd_above_by

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by
  apply Sequence.convergent_of_monotone
  . exact example_6_3_9_bdd_above
  . exact example_6_3_9_mono

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by
  have h := Sequence.lim_of_monotone example_6_3_9_bdd_above example_6_3_9_mono
  set L := lim (Example_6_3_9:Sequence)
  simp [Sequence.sup] at h
  symm at h
  have hb := example_6_3_9_bdd_above_by
  unfold Sequence.BddAboveBy at hb
  rw [← isLUB_iff_sSup_eq, isLUB_iff_le_iff] at h
  replace h := (h 4).mpr
  have h4 : (4:EReal) = (4:ℝ) := by rfl
  contrapose! h
  constructor
  . simp [upperBounds]
    intro _ n hn
    simp [hn]
    intro rfl
    specialize hb n (by simp [hn])
    simp [hn] at hb
    rw [h4]
    simp [hb]
  . rw [h4]
    simp [h]

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone
  . unfold Sequence.IsAntitone
    intro n hn
    simp [a] at hn
    have hn2 : 0 ≤ n+1 := by omega
    simp [a, hn, hn2]
    lift n to ℕ using hn
    simp
    rw [pow_succ]
    suffices h : x ^ n * x ≤ x ^ n * 1
    . linarith
    gcongr
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence)
  . have hconv2 : ((fun (n:ℕ) ↦ x^(n+1)):Sequence).Convergent := by sorry
    rw [Sequence.convergent_def] at *
    obtain ⟨ L, hL ⟩ := hconv
    obtain ⟨ M, hM ⟩ := hconv2
    obtain h := (Sequence.lim_eq.mp hL).2
    unfold a at *
    have h2 := (Sequence.lim_eq.mp hM).2
    rw [h, h2]; clear h h2
    have h := Sequence.tendsTo_sub hL hM
    suffices goal : ((↑fun n ↦ x ^ n) - ((fun (n:ℕ) ↦ x^(n+1)):Sequence)).TendsTo 0
    . rw [Sequence.lim_eq] at h goal
      linarith
    sorry
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by
  intro h
  replace h := Sequence.bounded_of_cauchy (Sequence.IsCauchy.convergent h)
  contrapose! h; clear h
  sorry

end Chapter6
