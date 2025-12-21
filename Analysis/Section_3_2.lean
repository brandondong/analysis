import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  set P : Object → Prop := fun x ↦ False
  choose A hA using h P
  use A
  simp [P] at hA
  exact hA

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  set P : Object → Prop := fun x' ↦ x' = x
  choose A hA using h P
  use A

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  set P : Object → Prop := fun y ↦ y = x₁ ∨ y = x₂
  choose A hA using h P
  use A

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  set P : Object → Prop := fun z ↦ z ∈ A ∨ z ∈ B
  choose A hA using h P
  use A

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  set P : Object → Prop := fun z ↦ ∃ h : z ∈ A, P ⟨ z, h ⟩
  choose A hA using h P
  use A

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (_hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  set P : Object → Prop := fun y ↦ ∃ a : A, P a y
  choose A hA using h P
  use A

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  -- Consider the singleton set {A}.
  -- Apply the regularity axiom on it which forces the selection to be A
  -- and so we know Disjoint A {A}.
  have h1 : ({(A: Object)}:Set) ≠ ∅
  . intro contra
    rw [SetTheory.Set.ext_iff] at contra
    simp at contra
  have h := axiom_of_regularity h1
  obtain ⟨ ⟨ a, haA ⟩, h ⟩ := h
  specialize h A
  rw [mem_singleton] at haA
  simp [haA, disjoint_iff, SetTheory.Set.ext_iff] at h
  intro contra
  specialize h A contra
  contradiction

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  -- Consider the set {A, B}.
  -- Apply the regularity axiom on it which forces the selection to be A or B
  -- and so we know Disjoint A {A, B} or Disjoint B {A, B}.
  have h1 : ({(A: Object), (B: Object)}:Set) ≠ ∅
  . intro contra
    rw [SetTheory.Set.ext_iff] at contra
    specialize contra A
    simp at contra
  have h := axiom_of_regularity h1
  obtain ⟨ ⟨ x, hxAB ⟩, h ⟩ := h
  rw [mem_pair] at hxAB
  obtain hxA | hxB := hxAB
  . specialize h A hxA
    simp [disjoint_iff, SetTheory.Set.ext_iff] at h
    specialize h B
    simp at h
    tauto
  . specialize h B hxB
    simp [disjoint_iff, SetTheory.Set.ext_iff] at h
    specialize h A
    simp at h
    tauto

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
  constructor
  . intro h
    set P : Object → Prop := fun x ↦ True
    choose S hS using h P
    simp [P] at hS
    use S
  . intro h
    -- Axiom of specification becomes universal with this set of everything.
    obtain ⟨ U, hU ⟩ := h
    unfold axiom_of_universal_specification
    intro P
    set S := U.specify (fun x ↦ P x.val)
    use S
    intro x
    have hs := specification_axiom' (fun (x:U.toSubtype) ↦ P x.val)
    specialize hU x
    specialize hs ⟨ x, hU ⟩
    exact hs

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  intro h
  rw [← univ_iff] at h
  exact Russells_paradox h


end Chapter3
