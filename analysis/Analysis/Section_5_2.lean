import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

lemma Rat.CloseSeq.coe (ε : ℚ) (a b:ℕ → ℚ) :
    ε.CloseSeq a b ↔ ∀ n, ε.Close (a n) (b n) := by
  constructor
  . intro h n
    have := h n (by simp) (by simp)
    simp at this
    exact this
  intro h n hn _
  simp at hn
  lift n to ℕ using hn
  simp
  exact h n

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.CloseSeq.coe]
  intro n
  simp [Rat.Close]
  ring_nf
  rw [abs_mul]
  have : |(-1:ℚ) / 10| = 1 / 10
  . rw [abs_of_neg]
    . norm_num
    . norm_num
  rw [this]
  have : |(-1:ℚ) ^ n| = 1
  . exact abs_neg_one_pow n
  simp [this]

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  simp
  use 0, 1
  simp [Rat.Close]
  ring_nf
  simp
  norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.Steady.coe]
  simp
  use 0, 1
  simp [Rat.Close]
  ring_nf
  rw [abs_of_nonneg] <;> norm_num

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [Rat.eventuallyClose_def]
  constructor <;> intro h
  . obtain ⟨ z, hz ⟩ := h
    obtain h | h := lt_or_ge z 0
    . use 0
      intro n _
      rw [Rat.closeSeq_def] at hz
      have hz2 : z ≤ ↑n := by omega
      specialize hz n (by simp [hz2]) (by simp [hz2])
      simp [hz2] at hz
      exact hz
    . lift z to ℕ using h
      use z
      rw [Rat.closeSeq_def] at hz
      intro n hn
      specialize hz n (by simp [hn]) (by simp [hn])
      simp [hn] at hz
      exact hz
  . obtain ⟨ N, hN ⟩ := h
    use N
    rw [Rat.closeSeq_def]
    intro z hz1 _
    simp at hz1
    have hz : z ≥ 0 := by omega
    lift z to ℕ using hz
    simp at hz1
    simp [hz1]
    exact hN z hz1

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.CloseSeq.coe]
  simp
  use 0
  simp [Rat.Close]
  ring_nf
  rw [abs_of_nonneg] <;> norm_num

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  use 1
  intro n hn
  ring_nf
  rw [abs_mul]
  rw [ge_iff_le, le_iff_exists_add] at hn
  obtain ⟨ x, rfl ⟩ := hn
  simp
  ring_nf
  rw [abs_of_nonneg]
  . induction' x with x IH
    . norm_num
    simp at IH ⊢
    have : (10:ℚ) ^ ((-2:ℤ) - (↑x + 1)) = 10 ^ ((-2:ℤ) - ↑x) * 10⁻¹
    . have : (-2:ℤ) - (↑x + 1) = (-2:ℤ) - ↑x - 1 := by omega
      rw [this]; clear this
      have : (10:ℚ) ≠ 0 := by norm_num
      exact zpow_sub_one₀ this (-2 - ↑x)
    rw [this]; clear this
    have : (10:ℚ) ^ ((-2:ℤ) - ↑x) * 10⁻¹ * 2 = 10 ^ ((-2:ℤ) - ↑x) * 2 * 10⁻¹ := by linarith
    rw [this]; clear this
    linarith
  . apply zpow_nonneg
    norm_num

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  use 2
  intro n hn
  ring_nf
  rw [abs_mul]
  rw [ge_iff_le, le_iff_exists_add] at hn
  obtain ⟨ x, rfl ⟩ := hn
  simp
  ring_nf
  rw [abs_of_nonneg]
  . induction' x with x IH
    . norm_num
    have : (-3:ℤ) - ↑(x + 1) = -3 - ↑x - 1 := by omega
    rw [this]; clear this
    have h10 : (10:ℚ) ≠ 0 := by norm_num
    have : (10:ℚ) ^ ((-3:ℤ) - ↑x - 1) = 10 ^ ((-3:ℤ) - ↑x) * 10⁻¹ := by exact zpow_sub_one₀ h10 _
    rw [this]; clear this
    linarith
  . apply zpow_nonneg
    norm_num

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [Sequence.equiv_def]
  constructor <;> intro h
  . intro e he
    specialize h e he
    rwa [Rat.eventuallyClose_iff] at h
  . intro e he
    rw [Rat.eventuallyClose_iff]
    exact h e he

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [mul_assoc, ←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  have helper (a b: ℕ → ℚ) (hab: Equiv a b) (ha: (a:Sequence).IsCauchy) : (b:Sequence).IsCauchy
  . rw [Sequence.IsCauchy.coe] at *
    intro e he
    rw [Sequence.equiv_iff] at hab
    -- b i - b j <= [b i - a i] + [a j - b j] + [a i - a j]
    have he3 : e / 3 > 0
    . linarith
    obtain ⟨ N1, hN1 ⟩ := hab (e/3) he3
    obtain ⟨ N2, hN2 ⟩ := ha (e/3) he3
    unfold Section_4_3.dist at *
    use N1+N2
    intro i hi j hj
    have : b i - b j = (b i - a i) + (a j - b j) + (a i - a j) := by ring
    rw [this]; clear this
    calc
      _ ≤ |b i - a i + (a j - b j)| + |(a i - a j)| := by exact abs_add_le _ _
      _ ≤ |b i - a i| + |(a j - b j)| + |(a i - a j)| := by {
        have := abs_add_le (b i - a i) (a j - b j)
        linarith
      }
      _ ≤ e/3 + e/3 + e/3 := by {
        have : |b i - a i| ≤ e/3
        . have := hN1 i (by omega)
          rw [← abs_neg]
          have : -(b i - a i) = a i - b i := by linarith
          rwa [this]
        have : |a j - b j| ≤ e/3
        . exact hN1 j (by omega)
        have : |a i - a j| ≤ e/3
        . exact hN2 i (by omega) j (by omega)
        linarith
      }
      _ ≤ _ := by linarith
  have symm : Equiv b a
  . rw [Sequence.equiv_iff] at *
    intro e he
    obtain ⟨ N, hN ⟩ := hab e he
    use N
    intro n hn
    specialize hN n hn
    rw [← abs_neg]
    have : (-(b n - a n)) = a n - b n := by ring
    rwa [this]
  constructor <;> intro h
  . exact helper a b hab h
  . exact helper b a symm h

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  -- Find the point where a and b are e-close.
  -- b is finite bounded up to that point. After that point, it's within e of a's bound.
  -- b n <= [b n - a n] + [a n]
  have helper {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) (ha: (a:Sequence).IsBounded) : (b:Sequence).IsBounded
  . rw [Rat.eventuallyClose_iff] at hab
    obtain ⟨ N, hN ⟩ := hab
    rw [Sequence.isBounded_def] at *
    simp only [Sequence.boundedBy_def] at *
    obtain ⟨ M, hM, hM2 ⟩ := ha
    obtain ⟨ P, hP, hP2 ⟩ := Sequence.finite_isBounded b N
    use M+P+|ε|
    have he : |ε| ≥ 0 := by simp
    constructor
    . linarith
    intro n
    obtain hn | hn := lt_or_ge n N
    . have := hP2 n (by omega)
      linarith
    . have : (b:Sequence).seq n = (b:Sequence).seq n - (a:Sequence).seq n + (a:Sequence).seq n := by ring
      rw [this]; clear this
      calc
        _ ≤ |(b:Sequence).seq n - (a:Sequence).seq n| + |(a:Sequence).seq n| := by exact abs_add _ _
        _ ≤ _ := by {
          have : |(b:Sequence).seq n - (a:Sequence).seq n| ≤ ε
          . rw [abs_sub_comm]
            have hn2 : n ≥ 0 := by omega
            lift n to ℕ using hn2
            simp at hn
            simp
            exact hN n hn
          have : |(a:Sequence).seq n| ≤ M
          . exact hM2 n
          have : ε ≤ |ε| := by exact le_abs_self ε
          linarith
        }
  have symm : ε.EventuallyClose ↑b ↑a
  . rw [Rat.eventuallyClose_iff] at *
    simp only [abs_sub_comm, hab]
  constructor <;> intro h
  . exact helper hab h
  . exact helper symm h

end Chapter5
