import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $`ε`-closeness, $`ε`-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from {lean}`ℤ` to {lean}`ℝ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from {lean}`ℕ` to {lean}`ℝ` can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  {given -show}`n₁, n₀`
  {lean}`a.from n₁` starts {lean}`a : Sequence` from {name}`n₁`.  It is intended for use when {lean}`n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence {name}`a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed {name}`a`, the function `ε ↦ ε.Steady s` is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed {name}`a`, the function `ε ↦ ε.EventuallySteady s` is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-- This is almost the same as {name}`Chapter5.Sequence.IsCauchy.coe` -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by
  rw [Real.steady_def, Rat.steady_def]
  constructor <;> intro h
  . intro n hn m hm
    rw [Real.close_def, Real.dist_eq]
    specialize h n (by {
      simp at hn
      exact hn
    }) m (by {
      simp at hm
      exact hm
    })
    unfold Rat.Close at h
    simp
    norm_cast
  . intro n hn m hm
    specialize h n (by {
      simp [hn]
    }) m (by {
      simp [hm]
    })
    rw [Real.close_def, Real.dist_eq] at h
    unfold Rat.Close
    simp at h
    norm_cast at h

theorem Sequence.from_cast (a: Chapter5.Sequence) (N : ℤ) : ((a.from N):Sequence) = ((a:Sequence).from N) := by
  ext x
  . rfl
  . simp
    by_cases h : a.n₀ ≤ x <;> simp [h]
    . by_cases h2 : N ≤ x <;> simp [h2]

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by
  rw [Rat.eventuallySteady_def, Real.eventuallySteady_def]
  constructor <;> intro h
  . obtain ⟨ N, hN1, hN2 ⟩ := h
    use N, hN1
    rw [Sequence.is_steady_of_rat] at hN2
    have := Sequence.from_cast a N
    rwa [← this]
  . obtain ⟨ N, hN1, hN2 ⟩ := h
    use N, hN1
    rw [Sequence.is_steady_of_rat]
    have := Sequence.from_cast a N
    rwa [this]

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
  rw [Sequence.tendsTo_def]
  simp_rw [Real.eventuallyClose_def, Real.closeSeq_def]
  constructor <;> intro h
  . intro e he
    specialize h e he
    obtain ⟨ N, hN1, hN2 ⟩ := h
    use N
    intro n hn
    have hn2 : n ≥ max a.m N
    . simp [hn]
      omega
    specialize hN2 n hn2
    simp [hn2] at hN2
    exact hN2
  . intro e he
    specialize h e he
    obtain ⟨ N, hN ⟩ := h
    use max a.m N
    constructor
    . simp
    . intro n hn
      have hn2 := hn
      simp at hn
      specialize hN n hn.2
      simp only [hn2]
      exact hN

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  gcongr <;> grind


/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by sorry

/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by sorry

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of {lean}`0` if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  rw [convergent_def] at h
  obtain ⟨ L, hL ⟩ := h
  rw [Sequence.isCauchy_def]
  intro e he
  rw [Real.eventuallySteady_def]
  rw [Sequence.tendsTo_def] at hL
  specialize hL (e/32) (by linarith)
  rw [Real.eventuallyClose_def] at hL
  obtain ⟨ N, hN1, hN2 ⟩ := hL
  use N, hN1
  rw [Real.steady_def]
  rw [Real.closeSeq_def] at hN2
  intro n hn m hm
  rw [Real.close_def]
  have h1 := hN2 n hn
  have h2 := hN2 m hm
  rw [Real.dist_eq] at *
  set c := (a.from N).seq n
  set d := (a.from N).seq m
  rw [abs_sub_comm] at h2
  have : c - d = (c - L) + (L - d) := by ring
  rw [this]
  have : |c - L + (L - d)| ≤ |c - L| + |(L - d)| := abs_add_le _ _
  linarith

/-- Example 6.1.13 -/
example : ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  rw [Real.eventuallySteady_def]
  push_neg
  intro N hN
  simp at hN
  rw [Real.steady_def]
  push_neg
  use N
  constructor
  . simp [hN]
  use N+1
  constructor
  . simp
    omega
  rw [Real.dist_eq]
  have hN2 : 0 ≤ N + 1 := by omega
  simp [hN, hN2]
  lift N to ℕ using hN
  simp
  sorry

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by sorry

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by sorry

theorem abs_cast_helper {a:Chapter5.Real} : Chapter5.Real.equivR |a| = |Chapter5.Real.equivR a| := by
  obtain h | h := lt_or_ge a 0
  . rw [abs_of_neg h, abs_of_neg]
    . have := Chapter5.Real.equivR_ordered_ring.map_neg a
      simp at this ⊢
      exact this
    contrapose! h
    rwa [Chapter5.Real.equivR_map_nonneg]
  . rw [abs_of_nonneg h, abs_of_nonneg]
    rwa [Chapter5.Real.equivR_map_nonneg] at h

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by
  rw [Sequence.tendsTo_def]
  intro e he
  rw [Real.eventuallyClose_def]
  have ha := Chapter5.Sequence.difference_approaches_zero h
  obtain ⟨ q, hq1, hq2 ⟩ := exists_pos_rat_lt he
  specialize ha q hq1
  obtain ⟨ N, hN ⟩ := ha
  use N
  constructor
  . simp
  rw [Real.closeSeq_def]
  intro n hn
  simp at hn
  rw [Real.dist_eq]
  have hn2 : 0 ≤ n := by omega
  simp [hn, hn2]
  lift n to ℕ using hn2
  simp at ⊢ hn
  have hr : (Chapter5.LIM a).toCut.toR = (Chapter5.LIM a).equivR := by rfl
  rw [hr]
  specialize hN n hn
  rw [abs_sub_comm]
  have hq := Chapter5.Real.equivR_ratCast (q:=q)
  have h1 : |Chapter5.Real.equivR (Chapter5.LIM a) - (a n)| = Chapter5.Real.equivR |Chapter5.LIM a - (a n)|
  . set d := a n
    set c := (Chapter5.LIM a)
    rw [abs_cast_helper]
    suffices h : Chapter5.Real.equivR c - ↑d = Chapter5.Real.equivR (c - ↑d)
    . rw [h]
    have := Chapter5.Real.equivR_ordered_ring.map_sub c d
    simp at this ⊢
    rw [this]
  have h2 : Chapter5.Real.equivR |Chapter5.LIM a - (a n)| ≤ q
  . set r := |Chapter5.LIM a - (a n)|
    replace hN : 0 ≤ q - r := by linarith
    rw [Chapter5.Real.equivR_map_nonneg] at hN
    have : Chapter5.Real.equivR (↑q - r) = q - Chapter5.Real.equivR r
    . have : Chapter5.Real.equivR (↑q - r) = Chapter5.Real.equivR.toFun q - Chapter5.Real.equivR r
      . have := Chapter5.Real.equivR_ordered_ring.map_sub q r
        simp at this
        simp [this]
        exact hq.symm
      rw [this]
      simp
      exact hq
    linarith
  linarith

/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

theorem Sequence.finite_bounded_helper (a:Sequence) (N : ℤ) (hN : N ≥ a.m) : ∃ M:ℝ, ∀ n<N, |a.seq n| ≤ M := by
  suffices h (n':ℕ) : ∃ M, ∀ n < (a.m + n'), |a.seq n| ≤ M
  . rw [ge_iff_le, le_iff_exists_nonneg_add] at hN
    obtain ⟨ c, hc1, hc2 ⟩ := hN
    lift c to ℕ using hc1
    specialize h c
    simp_rw [hc2] at h
    exact h
  clear hN N
  induction' n' with c IH
  . use 0
    intro n hn
    simp
    simp at hn
    exact a.vanish n hn
  obtain ⟨ M, hM ⟩ := IH
  use max M (|a (a.m + c)|)
  intro n hn
  obtain h | h := lt_or_ge n (a.m + c)
  . specialize hM n h
    simp [hM]
  replace h : a.m + ↑c = n := by omega
  rw [← h]
  simp

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  rw [Sequence.isCauchy_def] at h
  specialize h 1 (by norm_num)
  rw [Real.eventuallySteady_def] at h
  obtain ⟨ N, hN1, hN2 ⟩ := h
  rw [Sequence.isBounded_def]
  rw [Real.steady_def] at hN2
  obtain ⟨ M, hM ⟩ := Sequence.finite_bounded_helper a N hN1
  use max (|a.seq N| + 1) M
  constructor
  . simp
    left
    have := abs_nonneg (a.seq N)
    linarith
  . rw [Sequence.boundedBy_def]
    intro n
    obtain h | h := lt_or_ge n N
    . simp
      right
      exact hM n h
    . specialize hN2 N (by simp [hN1]) n (by simp [hN1, h])
      rw [Real.close_def, Real.dist_eq] at hN2
      simp [hN1, h] at hN2
      rw [abs_sub_comm] at hN2
      have : a.seq n = a.seq n - a.seq N + a.seq N := by ring
      rw [this]; clear this
      have := abs_add_le (a.seq n - a.seq N) (a.seq N)
      simp only [le_sup_iff]
      left
      linarith

/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  have := Sequence.IsCauchy.convergent h
  exact bounded_of_cauchy this

/-- Example 6.1.18 -/
theorem example_6_1_18_bounded : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]
  push_neg
  intro M hM
  rw [Sequence.boundedBy_def]
  push_neg
  obtain ⟨ n, hn ⟩ := exists_nat_gt M
  use n
  simp
  rw [abs_of_nonneg]
  . linarith
  . linarith

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  have h := example_6_1_18_bounded
  contrapose! h
  exact Sequence.bounded_of_convergent h

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

theorem Sequence.add_m (a b: Sequence) : (a + b).m = min a.m b.m := by rfl

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
  rw [Sequence.tendsTo_def] at *
  intro e he
  specialize ha (e/32) (by linarith)
  specialize hb (e/32) (by linarith)
  rw [Real.eventuallyClose_def] at *
  obtain ⟨ Na, hNa1, hNa2 ⟩ := ha
  obtain ⟨ Nb, hNb1, hNb2 ⟩ := hb
  use max Na Nb
  constructor
  . simp [Sequence.add_m, hNa1]
  rw [Real.closeSeq_def] at *
  intro n hn
  simp at hn
  obtain ⟨ hn, hna, hnb ⟩ := hn
  have hnam : a.m ≤ n := by omega
  have hnbm : b.m ≤ n := by omega
  specialize hNa2 n (by simp [hnam, hna])
  specialize hNb2 n (by simp [hnbm, hnb])
  rw [Real.dist_eq] at *
  simp [hn, hna, hnb]
  simp [hnam, hna] at hNa2
  simp [hnbm, hnb] at hNb2
  have : a.seq n + b.seq n - (L + M) = (a.seq n - L) + (b.seq n - M) := by ring
  rw [this]; clear this
  have := abs_add_le (a.seq n - L) (b.seq n - M)
  linarith

theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  obtain ⟨ M, hM ⟩ := hb
  have h := Sequence.tendsTo_add hL hM
  constructor
  . use L+M
  rw [Sequence.lim_eq] at *
  linarith

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

theorem Sequence.mul_m (a b: Sequence) : (a * b).m = min a.m b.m := by rfl

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(b) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
  rw [Sequence.tendsTo_def] at *
  intro e he
  suffices h : (min 1 e).EventuallyClose (a * b) (L * M)
  . have h1 : (min 1 e) ≤ e := by simp
    exact Real.EventuallyClose.mono h1 h
  set e := min 1 e
  replace he : e > 0 := by simp [e, he]
  replace he2 : e ≤ 1 := by simp [e]
  have he3 : e / 3 > 0 := by linarith
  have hL := abs_nonneg L
  have hM := abs_nonneg M
  specialize ha (e/3*(|M|+1)⁻¹) (by {
    have : (|M| + 1)⁻¹ > 0
    . simp
      linarith
    exact Left.mul_pos he3 this
  })
  specialize hb (e/3*(|L|+1)⁻¹) (by {
    have : (|L| + 1)⁻¹ > 0
    . simp
      linarith
    exact Left.mul_pos he3 this
  })
  rw [Real.eventuallyClose_def] at *
  obtain ⟨ N, hN1, hN2 ⟩ := ha
  obtain ⟨ P, hP1, hP2 ⟩ := hb
  use max N P
  constructor
  . simp [Sequence.mul_m]
    tauto
  rw [Real.closeSeq_def] at *
  intro n hn
  simp at hn
  obtain ⟨ hn, hn2, hn3 ⟩ := hn
  have hn4 : a.m ≤ n := by omega
  have hn5 : b.m ≤ n := by omega
  specialize hN2 n (by simp [hn4, hn2])
  specialize hP2 n (by simp [hn5, hn3])
  rw [Real.dist_eq] at *
  simp [hn, hn2, hn3]
  simp [hn4, hn2] at hN2
  simp [hn5, hn3] at hP2
  set c := a.seq n
  set d := b.seq n
  have : c*d - L*M = ((c-L)*(d-M)) + (M*(c - L) + L*(d - M)) := by ring
  rw [this]; clear this
  have h1 := abs_add_le ((c - L) * (d - M)) (M * (c - L) + L * (d - M))
  have h2 := abs_add_le (M * (c - L)) ( L * (d - M))
  rw [le_mul_inv_iff₀ (by linarith), mul_comm] at hN2
  rw [le_mul_inv_iff₀ (by linarith), mul_comm] at hP2
  have h3 : |(c - L) * (d - M)| ≤ e/3
  . rw [abs_mul]
    have he3 : e/3 > 0 := by linarith
    calc
      _ ≤ ((|M| + 1) * |c - L|) * |d - M| := by {
        gcongr
        have : 1 * |c - L| ≤ (|M| + 1) * |c - L|
        . gcongr
          linarith
        linarith
      }
      _ ≤ ((|M| + 1) * |c - L|) * ((|L| + 1) * |d - M|) := by {
        gcongr
        have : 1 * |d - M| ≤ (|L| + 1) * |d - M|
        . gcongr
          linarith
        linarith
      }
      _ ≤ (e/3) * ((|L| + 1) * |d - M|) := by {
        gcongr
      }
      _ ≤ (e/3) * (e/3) := by {
        gcongr
      }
      _ ≤ _ := by {
        have : e*e ≤ e*1
        . gcongr
        linarith
      }
  have h4 : |M * (c - L)| ≤ e/3
  . rw [abs_mul]
    have : |M| * |c - L| ≤ (|M|+1) * |c - L|
    . gcongr
      linarith
    linarith
  have h5 : |L * (d - M)| ≤ e/3
  . rw [abs_mul]
    have : |L| * |d - M| ≤ (|L| + 1) * |d - M|
    . gcongr
      linarith
    linarith
  linarith

theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  obtain ⟨ M, hM ⟩ := hb
  have h := Sequence.tendsTo_mul hL hM
  constructor
  . use L*M
  rw [Sequence.lim_eq] at *
  rw [h.2, hL.2, hM.2]


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

theorem Sequence.smul_m (c: ℝ) (a: Sequence) : (c • a).m = a.m := by rfl

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Theorem 6.1.19(c) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by
  set b:Sequence := (Sequence.mk' a.m fun _ ↦ c)
  have h1 : c • a = b * a
  . ext x
    . simp [Sequence.mul_m, b, Sequence.smul_m]
    . simp only [Sequence.smul_eval, b, Sequence.mul_eval]
      by_cases h : x ≥ a.m
      . simp [h]
      . simp [h]
        right
        exact a.vanish x (by omega)
  rw [h1]
  have hb: b.TendsTo c
  . rw [Sequence.tendsTo_def]
    intro e he
    rw [Real.eventuallyClose_def]
    use b.m, (by simp)
    rw [Real.closeSeq_def]
    intro n hn
    rw [Real.dist_eq]
    simp at hn
    simp [hn, b]
    linarith
  exact Sequence.tendsTo_mul hb ha

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  have h := Sequence.tendsTo_smul c hL
  constructor
  . use c * L
  rw [Sequence.lim_eq] at *
  rw [hL.2, h.2]

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

theorem Sequence.sub_m (a b: Sequence) : (a - b).m = min a.m b.m := by rfl

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(d) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
  set b':Sequence := (Sequence.mk' b.m fun x ↦ -(b.seq x))
  have hb': b'.TendsTo (-M)
  . clear ha L a
    rw [Sequence.tendsTo_def] at *
    intro e he
    specialize hb e he
    rw [Real.eventuallyClose_def] at *
    obtain ⟨ N, hN, hN2 ⟩ := hb
    use N
    constructor
    . simp [b', hN]
    rw [Real.closeSeq_def] at *
    intro n hn
    simp [b'] at hn
    specialize hN2 n (by simp [hn])
    rw [Real.dist_eq] at *
    simp [hn] at hN2
    simp [b', hn]
    rw [abs_sub_comm] at hN2
    have : -b.seq n + M = M - b.seq n := by ring
    rwa [this]
  have h1 : a - b = a + b'
  . ext x
    . simp [Sequence.sub_m, Sequence.add_m, b']
    simp [b']
    by_cases h : b.m ≤ x
    . simp [h]
      ring
    simp [h]
    exact b.vanish x (by omega)
  have h2 := Sequence.tendsTo_add ha hb'
  rw [h1]
  have : L - M = L + -M := by ring
  rwa [this]

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  obtain ⟨ M, hM ⟩ := hb
  have h := Sequence.tendsTo_sub hL hM
  constructor
  . use L-M
  rw [Sequence.lim_eq] at *
  linarith

noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

theorem Sequence.inv_m (a: Sequence) : (a⁻¹).m = a.m := by rfl

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(e) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
  rw [Sequence.tendsTo_def] at *
  intro e he
  have ha := ha
  have hL : |L| > 0 := abs_pos.mpr hnon
  specialize ha ((2⁻¹ * |L|) * (|L| * e)) (by {
    simp [hL, he]
  })
  rw [Real.eventuallyClose_def] at *
  obtain ⟨ N, hN, hN2 ⟩ := ha
  specialize ha (2⁻¹ * |L|) (by linarith)
  obtain ⟨ M, hM, hM2 ⟩ := ha
  use max N M
  constructor
  . simp [Sequence.inv_m, hN]
  rw [Real.closeSeq_def] at *
  intro n hn
  simp [Sequence.inv_m] at hn
  specialize hN2 n (by simp [hn])
  specialize hM2 n (by simp [hn])
  rw [Real.dist_eq] at *
  simp [Sequence.inv_m, hn]
  simp [hn] at hN2
  simp [hn] at hM2
  set b := a.seq n
  have hb : b ≠ 0
  . contrapose! hM2
    simp [hM2]
    linarith
  have hb2 : |b| > 0 := abs_pos.mpr hb
  suffices h : |b - L| ≤ |b| * (|L| * e)
  . have : |b| * (|L| * e) = e * (|b| * |L|) := by ring
    rw [abs_sub_comm, this, ← mul_inv_le_iff₀ (Left.mul_pos hb2 hL), ← abs_mul, ← abs_inv, ← abs_mul] at h; clear this
    have : b⁻¹ - L⁻¹ = (L - b) * (b * L)⁻¹
    . field_simp
    rwa [this]
  have h : (2⁻¹ * |L|) * (|L| * e) ≤ |b| * (|L| * e)
  . gcongr
    obtain h1 | h1 := lt_or_ge b 0 <;> obtain h2 | h2 := lt_or_ge L 0
    . simp [abs_of_neg h1, abs_of_neg h2]
      simp [abs_of_neg h2, abs_le] at hM2
      linarith
    . simp [abs_of_neg h1, abs_of_nonneg h2]
      simp [abs_of_nonneg h2, abs_le] at hM2
      linarith
    . simp [abs_of_nonneg h1, abs_of_neg h2]
      simp [abs_of_neg h2, abs_le] at hM2
      linarith
    . simp [abs_of_nonneg h1, abs_of_nonneg h2]
      simp [abs_of_nonneg h2, abs_le] at hM2
      linarith
  linarith

theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  have h : a⁻¹.TendsTo L⁻¹
  . apply Sequence.tendsTo_inv
    . exact hL
    rw [Sequence.lim_eq] at hL
    rwa [← hL.2]
  constructor
  . use L⁻¹
  rw [Sequence.lim_eq] at *
  rw [hL.2, h.2]

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

theorem Sequence.div_m (a b: Sequence) : (a / b).m = min a.m b.m := by rfl

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(f) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by
  have h1 : a / b = a * b⁻¹
  . ext x
    . simp [Sequence.div_m, Sequence.mul_m, Sequence.inv_m]
    simp
    ring
  rw [h1]
  have h2 := Sequence.tendsTo_inv hb hnon
  have h3 := Sequence.tendsTo_mul ha h2
  exact h3

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  obtain ⟨ M, hM ⟩ := hb
  have h := Sequence.tendsTo_div hL hM (by {
    rw [Sequence.lim_eq] at hM
    rwa [← hM.2]
  })
  constructor
  . use L/M
  rw [Sequence.lim_eq] at *
  rw [h.2, hL.2, hM.2]

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

theorem Sequence.max_m (a b: Sequence) : (a ⊔ b).m = min a.m b.m := by rfl

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(g) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
  wlog h : L ≤ M
  . replace h := this hb ha (by linarith); clear this
    have h1 : a ⊔ b = b ⊔ a
    . ext x
      . simp [Sequence.max_m, min_comm]
      simp [max_comm]
    rwa [h1, max_comm]
  -- If L = M, then both a and b must converge to L.
  rw [le_iff_eq_or_lt'] at h
  obtain rfl | h := h
  . simp
    rw [Sequence.tendsTo_def] at *
    intro e he
    specialize ha e he
    specialize hb e he
    rw [Real.eventuallyClose_def] at *
    obtain ⟨ N, hN, hN2 ⟩ := ha
    obtain ⟨ P, hP, hP2 ⟩ := hb
    use max N P
    constructor
    . simp [Sequence.max_m, hN]
    rw [Real.closeSeq_def] at *
    intro n hn
    simp at hn
    have hna : a.m ≤ n := by omega
    have hnb : b.m ≤ n := by omega
    specialize hN2 n (by simp [hna, hn])
    specialize hP2 n (by simp [hnb, hn])
    rw [Real.dist_eq] at *
    simp [hna, hn] at hN2
    simp [hnb, hn] at hP2
    simp [hn]
    obtain h | h := lt_or_ge (a.seq n) (b.seq n)
    . replace h : a.seq n ≤ b.seq n := by linarith
      simp [h, hP2]
    . simp [h, hN2]
  -- If L < M, then there exists c where L+c = M.
  rw [lt_iff_exists_pos_add] at h
  obtain ⟨ c, hc, rfl ⟩ := h
  have : L+c ≥ L := by linarith
  simp [this]; clear this
  -- We can use c to find some N where b > a for all n >= N.
  rw [Sequence.tendsTo_def] at *
  intro e he
  specialize ha (c/4) (by linarith)
  specialize hb (min e (c/4)) (by simp [he, hc])
  rw [Real.eventuallyClose_def] at *
  obtain ⟨ N, hN, hN2 ⟩ := ha
  obtain ⟨ M, hM, hM2 ⟩ := hb
  use max N M
  constructor
  . simp [Sequence.max_m, hN]
  rw [Real.closeSeq_def] at *
  intro n hn
  simp at hn
  have hna : a.m ≤ n := by omega
  have hnb : b.m ≤ n := by omega
  specialize hN2 n (by simp [hna, hn])
  specialize hM2 n (by simp [hnb, hn])
  rw [Real.dist_eq] at *
  simp [hna, hn] at hN2
  simp [hnb, hn] at hM2
  simp [hn]
  have h : b.seq n ≥ a.seq n
  . replace hM2 := hM2.2
    rw [abs_le] at *
    linarith
  simp [h, hM2]

theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  obtain ⟨ M, hM ⟩ := hb
  have h := Sequence.tendsTo_max hL hM
  constructor
  . use max L M
  rw [Sequence.lim_eq] at *
  rw [h.2, hL.2, hM.2]

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

theorem Sequence.min_m (a b: Sequence) : (a ⊓ b).m = min a.m b.m := by rfl

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
  have h1 : min a b = (-1:ℝ) • (max ((-1:ℝ) • a) ((-1:ℝ) • b))
  . ext x
    . simp [Sequence.min_m, Sequence.smul_m, Sequence.max_m]
    simp
    obtain h | h := lt_or_ge (a.seq x) (b.seq x)
    . replace h : a.seq x ≤ b.seq x := by linarith
      simp [h]
    simp [h]
  rw [h1]
  have h2 := Sequence.tendsTo_smul (-1) ha
  have h3 := Sequence.tendsTo_smul (-1) hb
  have h4 := Sequence.tendsTo_max h2 h3
  have h5 := Sequence.tendsTo_smul (-1) h4
  have h6 : min L M = (-1 * max (-1 * L) (-1 * M))
  . simp
    obtain h | h := lt_or_ge L M
    . replace h : L ≤ M := by linarith
      simp [h]
    . simp [h]
  rwa [h6]

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
  rw [Sequence.convergent_def] at *
  obtain ⟨ L, hL ⟩ := ha
  obtain ⟨ M, hM ⟩ := hb
  have h := Sequence.tendsTo_min hL hM
  constructor
  . use min L M
  rw [Sequence.lim_eq] at *
  rw [h.2, hL.2, hM.2]

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by
  rw [gt_iff_lt, lt_iff_exists_pos_add] at hnm
  obtain ⟨ c, hc, rfl ⟩ := hnm
  rw [← Nat.exists_add_one_eq] at hc
  obtain ⟨ c, rfl ⟩ := hc
  induction' c with c IH
  . simp
    exact ha n
  specialize ha (n + (c + 1))
  have : n + (c + 1 + 1) = (n + (c + 1) + 1) := by ring
  rw [this]
  linarith

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
  rw [Sequence.tendsTo_def, Sequence.tendsTo_def]
  constructor <;> intro h e he <;> specialize h e he <;>
    rw [Real.eventuallyClose_def] at * <;> obtain ⟨ N, hN, hN2 ⟩ := h
  . use max N m
    constructor
    . simp [hN]
      omega
    rw [Real.closeSeq_def] at *
    intro n hn
    simp at hn
    specialize hN2 n (by simp [hn])
    rw [Real.dist_eq] at *
    simp [hn] at hN2
    simp [hn, hN2]
  . simp at hN
    use N
    constructor
    . simp [hN]
    rw [Real.closeSeq_def] at *
    intro n hn
    simp at hn
    have hn2 : m ≤ n := by omega
    specialize hN2 n (by simp [hn, hn2])
    rw [Real.dist_eq] at *
    simp [hn, hn2] at hN2
    simp [hn, hN2]

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
  rw [Sequence.tendsTo_def, Sequence.tendsTo_def]
  constructor <;> intro h e he <;> specialize h e he <;>
    rw [Real.eventuallyClose_def] at * <;> obtain ⟨ N, hN, hN2 ⟩ := h
  . use N
    constructor
    . simp [hN]
    rw [Real.closeSeq_def] at *
    intro n hn
    simp at hn
    have hn2 : a.m ≤ n + ↑k ∧ N ≤ n + ↑k := by omega
    specialize hN2 (n+k) (by simp [hn2])
    rw [Real.dist_eq] at *
    simp [hn2] at hN2
    simp [hn, hN2]
  . simp at hN
    use N+k
    constructor
    . omega
    rw [Real.closeSeq_def] at *
    intro n hn
    simp at hn
    have hn2 : a.m ≤ n - ↑k ∧ N ≤ n - ↑k := by omega
    specialize hN2 (n-k) (by simp [hn2])
    rw [Real.dist_eq] at *
    simp [hn2] at hN2
    simp [hn, hN2]

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by
  rw [Sequence.isBounded_def, Chapter5.Sequence.isBounded_def]
  constructor <;> intro ⟨ M, hM, h ⟩
  . use M
    constructor
    . norm_cast
    rw [Sequence.boundedBy_def]
    rw [Chapter5.Sequence.boundedBy_def] at h
    intro n
    specialize h n
    simp
    norm_cast
  . obtain ⟨ q, hq ⟩ := exists_rat_gt M
    use q
    constructor
    . have : (q:ℝ) ≥ 0 := by linarith
      norm_cast at this
    rw [Sequence.boundedBy_def] at h
    rw [Chapter5.Sequence.boundedBy_def]
    intro n
    specialize h n
    simp at h
    have : |↑(a.seq n)| ≤ (q:ℝ) := by linarith
    norm_cast at this

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
  set a:Sequence := Sequence.ofNatFun fun _ ↦ 1
  have ha : a.Convergent
  . unfold a
    rw [Sequence.convergent_def]
    use 1
    rw [Sequence.tendsTo_iff]
    intro e he
    use 0
    intro n hn
    simp [hn]
    linarith
  have hb := Sequence.lim_harmonic
  set b:Sequence := ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence)
  use a, b, ha, hb.1, hb.2
  push_neg
  intro h
  replace h := Sequence.bounded_of_cauchy (Sequence.IsCauchy.convergent h)
  contrapose! h; clear h
  intro M hM
  rw [Sequence.boundedBy_def]
  push_neg
  unfold a b
  simp
  obtain ⟨ n, hn2 ⟩ := exists_int_gt M
  have hn : 0 ≤ n
  . have : 0 ≤ (n:ℝ) := by linarith
    norm_cast at this
  use n
  simp [hn]
  rw [abs_of_nonneg (by {
    norm_cast
    simp
  })]
  have : (n.toNat:ℝ) = n
  . norm_cast
    simp [hn]
  rw [this]
  linarith

theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  rw [Sequence.isCauchy_of_rat, Sequence.isCauchy_def]
  simp_rw [Real.eventuallySteady_def]
  constructor <;> intro h e he <;> specialize h e he <;> obtain ⟨ N, hN, hN2 ⟩ := h <;> use N
  . rw [Real.steady_def] at hN2
    use hN
    intro n hn m hm
    have hn2 : a.n₀ ≤ n := by omega
    have hm2 : a.n₀ ≤ m := by omega
    specialize hN2 n (by simp [hn, hn2]) m (by simp [hm, hm2])
    rw [Real.close_def, Real.dist_eq] at hN2
    simp [hn, hn2, hm, hm2] at hN2
    simp [hN2]
  . use hN
    rw [Real.steady_def]
    intro n hn m hm
    simp at hn hm
    specialize hN2 n hn.2 m hm.2
    rw [Real.close_def, Real.dist_eq]
    simp [hn, hm]
    simp at hN2
    exact hN2
end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by
  rw [Chapter5.Sequence.equiv_iff]
  unfold Chapter5.Sequence.RatEquiv Real.SeqEventuallyClose Real.SeqCloseSeq
  constructor <;> intro h e he
  . obtain ⟨ q, hq1, hq2 ⟩ := exists_pos_rat_lt he
    specialize h q hq1
    obtain ⟨ N, hN ⟩ := h
    use N
    intro n hn1 _
    rw [Real.close_def, Real.dist_eq]
    simp at hn1
    have hn2 : n ≥ 0 := by omega
    simp [hn1, hn2]
    lift n to ℕ using hn2
    simp
    simp at hn1
    specialize hN n hn1
    suffices h : |a n - b n| ≤ (q:ℝ)
    . simp at h
      linarith
    norm_cast
  . have he2 : e > (0:ℝ)
    . norm_cast
    specialize h e he2
    obtain ⟨ N, hN ⟩ := h
    use N.toNat
    intro n hn
    have hn2 : N ≤ ↑n
    . omega
    specialize hN n (by simp [hn2]) (by simp [hn2])
    rw [Real.close_def, Real.dist_eq] at hN
    simp [hn2] at hN
    norm_cast at hN

end Chapter6
