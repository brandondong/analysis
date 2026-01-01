import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as `Set.pi` and `Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  rw [SetTheory.Set.ext_iff]
  constructor <;> intro h
  . have ha := h a
    have hb := h b
    simp at *
    tauto
  . intro x
    simp [h]

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by {
    intro p1 p2
    simp
    intro h
    rw [SetTheory.Set.ext_iff] at h
    rw [OrderedPair.eq]
    have hfst : p1.fst = p2.fst
    . have hp1 := h (({p1.fst}:Set):Object)
      simp at hp1
      obtain hp1 | hp1 := hp1
      . rw [SetTheory.Set.ext_iff] at hp1
        specialize hp1 p1.fst
        simp at hp1
        exact hp1
      . symm at hp1
        simp [pair_eq_singleton_iff] at hp1
        tauto
    use hfst
    have hp1_snd := h (({p1.fst, p1.snd}:Set):Object)
    simp at hp1_snd
    obtain hp1 | hp1 := hp1_snd
    . rw [pair_eq_singleton_iff] at hp1
      obtain ⟨ _, hp1 ⟩ := hp1
      specialize h (({p2.fst, p2.snd}:Set):Object)
      simp at h
      rw [← hp1] at hfst
      rw [hfst] at h
      simp [pair_eq_singleton_iff] at h
      tauto
    . rw [SetTheory.Set.ext_iff] at hp1
      specialize hp1 p1.snd
      simp at hp1
      obtain hp1 | hp1 := hp1
      . rw [← hp1] at hfst
        specialize h (({p2.fst, p2.snd}:Set):Object)
        simp at h
        rw [hfst] at h
        simp [pair_eq_singleton_iff] at h
        tauto
      . exact hp1
  }

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by grind))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- This equips an `OrderedPair` with proofs that `x ∈ X` and `y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  Connections with the Mathlib set product, which consists of Lean pairs like `(x, y)`
  equipped with a proof that `x` is in the left set, and `y` is in the right set.
  Lean pairs like `(x, y)` are similar to our `OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun p ↦ mk_cartesian (snd p) (fst p)
  invFun := fun p ↦ mk_cartesian (snd p) (fst p)
  left_inv := by {
    intro p
    simp
  }
  right_inv := by {
    intro p
    simp
  }

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f ⟨ (⟨ x, y ⟩:OrderedPair), by simp ⟩
  left_inv _ := by simp
  right_inv _ := by simp [←pair_eq_fst_snd]

/-- Definition 3.5.6.  The indexing set `I` plays the role of `{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
  -- tuple takes a function from Xi index which outputs some element in Xi.
  -- tuple is that same function but with a proof that the output is in iUnion I X
  -- iProd is a set of all such possible tuple functions.
  constructor <;> intro h
  . ext i
    unfold tuple at h
    simp at h
    rw [funext_iff] at h
    specialize h i
    simp at h
    exact h
  . unfold tuple
    simp
    ext i
    rw [funext_iff] at h
    specialize h i
    simp [h]

/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

abbrev singleton_iProd_inv (i:Object) (X:Set) : X → iProd (fun _:({i}:Set) ↦ X) :=
  fun x ↦ ⟨ tuple ((fun _:({i}:Set) ↦ x)), by {
    rw [mem_iProd]
    use fun _:({i}:Set) ↦ x
  } ⟩

theorem singleton_iProd_inv_surjective (i:Object) (X:Set) : Function.Surjective (singleton_iProd_inv i X) := by
  intro ⟨ t, ht ⟩
  rw [mem_iProd] at ht
  obtain ⟨ f, hx ⟩ := ht
  unfold singleton_iProd_inv
  set x := f ⟨ i, (by simp) ⟩
  use x
  simp
  rw [hx, tuple_inj]
  ext x'
  have hx' : x' = ⟨ i, (by simp) ⟩ := by aesop
  simp [hx']
  unfold x
  simp

theorem singleton_iProd_inv_injective (i:Object) (X:Set) : Function.Injective (singleton_iProd_inv i X) := by
  intro x1 x2 h
  unfold singleton_iProd_inv at h
  simp at h
  rw [funext_iff] at h
  specialize h ⟨ i, (by simp) ⟩
  simp at h
  exact (coe_inj X x1 x2).mp h

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
  -- iProd is a set of all possible tuple functions taking an index (1 possibility) and outputting
  -- some element in X (|X| possibilities).
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun := Function.surjInv (singleton_iProd_inv_surjective i X)
  invFun := singleton_iProd_inv i X
  left_inv := by {
    change Function.RightInverse (Function.surjInv (singleton_iProd_inv_surjective i X)) (singleton_iProd_inv i X)
    apply Function.rightInverse_surjInv
  }
  right_inv := by {
    change Function.LeftInverse (Function.surjInv (singleton_iProd_inv_surjective i X)) (singleton_iProd_inv i X)
    apply Function.leftInverse_surjInv
    constructor
    . exact singleton_iProd_inv_injective i X
    . exact singleton_iProd_inv_surjective i X
  }

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  -- iProd is a set of all possible tuple functions taking an element of the empty set (empty domain)
  -- and so there is only one possible such function.
  toFun := fun x ↦ ()
  -- t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x
  invFun := fun _u ↦ ⟨ tuple ((fun e ↦ ⟨ 1, by {
    have contra := e.2
    simp at contra
  } ⟩): ∀ i, X i), by {
    rw [mem_iProd]
    use (fun e ↦ ⟨ 1, by {
      have contra := e.2
      simp at contra
    } ⟩)
  } ⟩
  left_inv := by {
    intro ⟨ t, ht ⟩
    rw [mem_iProd] at ht
    obtain ⟨ f, hf ⟩ := ht
    simp [hf]
    ext e
    have contra := e.2
    simp at contra
  }
  right_inv := by {
    intro u
    simp
  }

abbrev iProd_of_const_inv (I:Set) (X: Set) : (I → X) → (iProd (fun _:I ↦ X)) :=
  fun f ↦ ⟨ tuple f, by {
    rw [mem_iProd]
    use f
  } ⟩

theorem iProd_of_const_inv_surjective (I:Set) (X: Set) : Function.Surjective (iProd_of_const_inv I X) := by
  intro ⟨ t, ht ⟩
  rw [mem_iProd] at ht
  unfold iProd_of_const_inv
  obtain ⟨ f, hf ⟩ := ht
  use f
  simp [hf]

theorem iProd_of_const_inv_injective (I:Set) (X: Set) : Function.Injective (iProd_of_const_inv I X) := by
  intro f1 f2 h
  unfold iProd_of_const_inv at h
  replace h : tuple f1 = tuple f2
  . exact congrArg Subtype.val h
  exact (tuple_inj f1 f2).mp h

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun _:I ↦ X) ≃ (I → X) where
  -- iProd is a set of all possible tuple functions taking an element of I
  -- and outputting some element in X
  toFun := Function.surjInv (iProd_of_const_inv_surjective I X)
  invFun := iProd_of_const_inv I X
  left_inv := by {
    change Function.RightInverse (Function.surjInv (iProd_of_const_inv_surjective I X)) (iProd_of_const_inv I X)
    apply Function.rightInverse_surjInv
  }
  right_inv := by {
    change Function.LeftInverse (Function.surjInv (iProd_of_const_inv_surjective I X)) (iProd_of_const_inv I X)
    apply Function.leftInverse_surjInv
    constructor
    . exact iProd_of_const_inv_injective I X
    . exact iProd_of_const_inv_surjective I X
  }

noncomputable abbrev pair_iProd_equiv_prod (X: ({0,1}:Set) → Set) : (iProd X) → (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) :=
  fun t ↦ ⟨ (⟨ ((mem_iProd _).mp t.property).choose ⟨ 0, by simp ⟩, ((mem_iProd _).mp t.property).choose ⟨ 1, by simp ⟩ ⟩:OrderedPair), by {
    rw [mem_cartesian]
    obtain ⟨ t, ht ⟩ := t
    set t_mem := ((mem_iProd _).mp ht)
    have ht_choose := t_mem.choose_spec
    rw [mem_iProd] at ht
    obtain ⟨ f, hf ⟩ := ht
    rw [ht_choose, tuple_inj] at hf
    rw [hf]
    use f ⟨ 0, by simp ⟩, f ⟨ 1, by simp ⟩
  } ⟩

noncomputable abbrev triple_iProd_equiv_prod (X: ({0,1,2}:Set) → Set) : (iProd X) → (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) :=
  fun t ↦ ⟨ (⟨ ((mem_iProd _).mp t.property).choose ⟨ 0, by simp ⟩,
    (⟨ ((mem_iProd _).mp t.property).choose ⟨ 1, by simp ⟩, ((mem_iProd _).mp t.property).choose ⟨ 2, by simp ⟩ ⟩:OrderedPair) ⟩:OrderedPair), by {
    rw [mem_cartesian]
    obtain ⟨ t, ht ⟩ := t
    set t_mem := ((mem_iProd _).mp ht)
    have ht_choose := t_mem.choose_spec
    rw [mem_iProd] at ht
    obtain ⟨ f, hf ⟩ := ht
    rw [ht_choose, tuple_inj] at hf
    rw [hf]
    use f ⟨ 0, by simp ⟩
    use ⟨ (⟨ f ⟨ 1, by simp ⟩, f ⟨ 2, by simp ⟩ ⟩:OrderedPair), by {
      rw [mem_cartesian]
      use f ⟨ 1, by simp ⟩, f ⟨ 2, by simp ⟩
    } ⟩
  } ⟩

open Classical in
theorem pair_iProd_equiv_prod_surjective (X: ({0,1}:Set) → Set) : Function.Surjective (pair_iProd_equiv_prod X) := by
  intro ⟨ p, hp ⟩
  rw [mem_cartesian] at hp
  obtain ⟨ x0, x1, hx ⟩ := hp
  -- Use the tuple that maps 0 -> x0 and 1 -> x1.
  set f : ∀ i, X i := fun i ↦ if hi : i = ⟨ 0, by simp ⟩ then ⟨ x0, by aesop ⟩ else ⟨ x1, by {
    suffices hi2 : i = ⟨ 1, by simp ⟩
    . simp [hi2, x1.2]
    aesop
  } ⟩
  have htf : tuple f ∈ iProd X
  . rw [mem_iProd]
    use f
  use ⟨ tuple f, htf ⟩
  unfold pair_iProd_equiv_prod
  simp [hx]
  set c := pair_iProd_equiv_prod._proof_3 X ⟨tuple f, htf⟩
  have c_choose := c.choose_spec
  rw [tuple_inj] at c_choose
  simp [← c_choose]
  unfold f
  simp

open Classical in
theorem triple_iProd_equiv_prod_surjective (X: ({0,1,2}:Set) → Set) : Function.Surjective (triple_iProd_equiv_prod X) := by
  intro ⟨ p, hp ⟩
  rw [mem_cartesian] at hp
  obtain ⟨ x0, ⟨ p2, hp2 ⟩, hx ⟩ := hp
  rw [mem_cartesian] at hp2
  obtain ⟨ x1, x2, hx2 ⟩ := hp2
  -- Use the tuple that maps 0 -> x0, 1 -> x1, and 2 -> x2.
  set f : ∀ i, X i := fun i ↦ if hi0 : i = ⟨ 0, by simp ⟩ then ⟨ x0, by aesop ⟩ else
    if hi1 : i = ⟨ 1, by simp ⟩ then ⟨ x1, by aesop ⟩ else
    if hi2 : i = ⟨ 2, by simp ⟩ then ⟨ x2, by aesop ⟩ else ⟨ 1, by {
      have hi := i.2
      simp at hi
      push_neg at hi0
      push_neg at hi1
      push_neg at hi2
      aesop
    } ⟩
  have htf : tuple f ∈ iProd X
  . rw [mem_iProd]
    use f
  use ⟨ tuple f, htf ⟩
  unfold triple_iProd_equiv_prod
  set c := triple_iProd_equiv_prod._proof_4 X ⟨tuple f, htf⟩
  have c_choose := c.choose_spec
  rw [tuple_inj] at c_choose
  simp [← c_choose]
  rw [hx]
  unfold f
  simp [hx2]

theorem pair_iProd_equiv_prod_injective (X: ({0,1}:Set) → Set) : Function.Injective (pair_iProd_equiv_prod X) := by
  intro ⟨ t1, ht1 ⟩ ⟨ t2, ht2 ⟩ h
  rw [mem_iProd] at *
  obtain ⟨ f1, hf1 ⟩ := ht1
  obtain ⟨ f2, hf2 ⟩ := ht2
  simp
  rw [hf1, hf2, tuple_inj]
  unfold pair_iProd_equiv_prod at h
  simp at h
  obtain ⟨ h0, h1 ⟩ := h
  set f1_choose := pair_iProd_equiv_prod._proof_3 X ⟨t1, ht1⟩
  set f2_choose := pair_iProd_equiv_prod._proof_3 X ⟨t2, ht2⟩
  have hf1c := f1_choose.choose_spec
  have hf2c := f2_choose.choose_spec
  simp at hf1c
  simp at hf2c
  rw [hf1c] at hf1
  rw [hf2c] at hf2
  rw [tuple_inj] at *
  rw [hf1, hf2] at *
  ext i
  have hi := i.2
  simp at hi
  set zero: ({0, 1}:Set) := ⟨ 0, by simp ⟩
  set one: ({0, 1}:Set) := ⟨ 1, by simp ⟩
  change i.val = zero.val ∨ i.val = one.val at hi
  rw [coe_inj, coe_inj] at hi
  obtain hi | hi := hi <;> rwa [hi]

theorem triple_iProd_equiv_prod_injective (X: ({0,1,2}:Set) → Set) : Function.Injective (triple_iProd_equiv_prod X) := by
  intro ⟨ t1, ht1 ⟩ ⟨ t2, ht2 ⟩ h
  rw [mem_iProd] at *
  obtain ⟨ f1, hf1 ⟩ := ht1
  obtain ⟨ f2, hf2 ⟩ := ht2
  simp
  rw [hf1, hf2, tuple_inj]
  unfold triple_iProd_equiv_prod at h
  set f1_choose := triple_iProd_equiv_prod._proof_4 X ⟨t1, ht1⟩
  set f2_choose := triple_iProd_equiv_prod._proof_4 X ⟨t2, ht2⟩
  have hf1c := f1_choose.choose_spec
  have hf2c := f2_choose.choose_spec
  simp at hf1c
  simp at hf2c
  rw [hf1c] at hf1
  rw [hf2c] at hf2
  rw [tuple_inj] at *
  simp at h
  obtain ⟨ h0, h1, h2 ⟩ := h
  rw [hf1, hf2] at *
  ext i
  have hi := i.2
  simp at hi
  set zero: ({0, 1, 2}:Set) := ⟨ 0, by simp ⟩
  set one: ({0, 1, 2}:Set) := ⟨ 1, by simp ⟩
  set two: ({0, 1, 2}:Set) := ⟨ 2, by simp ⟩
  change i.val = zero.val ∨ i.val = one.val ∨ i.val = two.val at hi
  rw [coe_inj, coe_inj, coe_inj] at hi
  obtain hi | hi | hi := hi <;> rwa [hi]

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  -- iProd is a set of all possible tuple functions taking an element of {0,1}
  -- and outputting some element in X0/X1
  toFun := pair_iProd_equiv_prod X
  invFun := Function.surjInv (pair_iProd_equiv_prod_surjective X)
  left_inv := by {
    apply Function.leftInverse_surjInv
    constructor
    . exact pair_iProd_equiv_prod_injective X
    . exact pair_iProd_equiv_prod_surjective X
  }
  right_inv := by apply Function.rightInverse_surjInv

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  -- Same as above but worse...
  toFun := triple_iProd_equiv_prod X
  invFun := Function.surjInv (triple_iProd_equiv_prod_surjective X)
  left_inv := by {
    apply Function.leftInverse_surjInv
    constructor
    . exact triple_iProd_equiv_prod_injective X
    . exact triple_iProd_equiv_prod_surjective X
  }
  right_inv := by apply Function.rightInverse_surjInv

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

/-- Connections with Mathlib's `Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

#check SetTheory.Set.axiom_of_regularity

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by {
    intro p1 p2 h
    simp at h
    rw [OrderedPair.eq]
    simp [SetTheory.Set.ext_iff] at h
    -- For fst, think about how the bijection forms.
    -- There is the happy case they line up.
    -- Otherwise p1.fst = {p2.fst, p2.snd} and p2.fst = {p1.fst, p1.snd}.
    -- This is a contradiction to be shown by axiom of regularity.
    -- Consider the set {p1.fst, p2.fst}. Either choice breaks it.
    have helper : p1.fst = ({p2.fst, p2.snd}:Set) → p2.fst = ({p1.fst, p1.snd}:Set) → False
    . intro hp1fst hp2fst
      have hr : ({p1.fst, p2.fst}:Set) ≠ ∅
      . simp
        rw [SetTheory.Set.ext_iff]
        simp
        use p2.fst
        tauto
      replace hr := SetTheory.Set.axiom_of_regularity hr
      obtain ⟨ ⟨ x, hx ⟩, hr ⟩ := hr
      simp at hx
      obtain hx | hx := hx
      . specialize hr ({p2.fst, p2.snd}:Set)
        simp at hr
        rw [hx] at hr
        specialize hr hp1fst
        rw [disjoint_iff, SetTheory.Set.ext_iff] at hr
        specialize hr p2.fst
        simp at hr
      . specialize hr ({p1.fst, p1.snd}:Set)
        simp at hr
        rw [hx] at hr
        specialize hr hp2fst
        rw [disjoint_iff, SetTheory.Set.ext_iff] at hr
        specialize hr p1.fst
        simp at hr
    have hp1fst := h p1.fst
    have hp2fst := h p2.fst
    have hp1snd := h ({p1.fst, p1.snd}:Set)
    have hp2snd := h ({p2.fst, p2.snd}:Set)
    simp at *
    have hfst : p1.fst = p2.fst
    . obtain hp1fst | hp1fst := hp1fst
      . exact hp1fst
      obtain hp2fst | hp2fst := hp2fst
      . exact hp2fst.symm
      have := helper hp1fst hp2fst
      contradiction
    use hfst
    clear hp1fst hp2fst h
    -- For snd, if they line up as {p1.fst, p1.snd} = {p2.fst, p2.snd},
    -- we know p1.fst = p2.fst and that is enough to get the other equality.
    have hsnd : ({p1.fst, p1.snd}:Set) = {p2.fst, p2.snd} → p1.snd = p2.snd
    . intro h
      rw [SetTheory.Set.ext_iff] at h
      simp at h
      have h1 := h p1.snd
      simp at h1
      obtain h1 | h1 := Or.symm h1
      . exact h1
      have h2 := h p2.snd
      simp at h2
      obtain h2 | h2 := Or.symm h2
      . exact h2.symm
      rw [h1, ← hfst, h2]
    obtain hp1snd | hp1snd := Or.symm hp1snd
    . exact hsnd hp1snd
    obtain hp2snd | hp2snd := Or.symm hp2snd
    . exact hsnd hp2snd.symm
    -- Otherwise, we reach the contradictory case again.
    have := helper hp2snd.symm hp1snd.symm
    contradiction
  }

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
  constructor <;> intro h
  . rw [Tuple.ext_iff] at h
    exact h.2
  . suffices hX : t.X = t'.X
    . exact ext hX h
    -- To prove the sets are equivalent, each element is mapped by some Fin n.
    -- Then we can just apply the opposite function to that same element.
    ext x
    constructor <;> intro hx
    . have hsurj := t.surj ⟨ x, hx ⟩
      obtain ⟨ i, hi ⟩ := hsurj
      specialize h i
      replace hi := congrArg Subtype.val hi
      simp at hi
      rw [← hi, h]
      exact Subtype.property _
    . have hsurj := t'.surj ⟨ x, hx ⟩
      obtain ⟨ i, hi ⟩ := hsurj
      specialize h i
      replace hi := congrArg Subtype.val hi
      simp at hi
      rw [← hi, ← h]
      exact Subtype.property _

abbrev tuple_equiv (n:ℕ) (X: SetTheory.Set.Fin n → Set) : { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } → (iProd X) :=
  fun t ↦ ⟨ tuple (fun i:SetTheory.Set.Fin n ↦ (⟨ t.val.x i, by exact t.2 i ⟩:X i) ), by {
    rw [mem_iProd]
    use (fun i:SetTheory.Set.Fin n ↦ (⟨ t.val.x i, by exact t.2 i ⟩:X i) )
  } ⟩

#check SetTheory.Set.image
-- X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

theorem tuple_equiv_surjective (n:ℕ) (X: SetTheory.Set.Fin n → Set) : Function.Surjective (tuple_equiv n X) := by
  intro ⟨ t, ht ⟩
  rw [mem_iProd] at ht
  obtain ⟨ f, hf ⟩ := ht
  -- Define some Tuple whose function maps to everything f hits.
  use ⟨ ⟨ (SetTheory.Set.Fin n).replace (P := fun x y ↦ f x = y) (by simp_all), -- Image set doesn't work...
    fun i ↦ ⟨ f i, by {
      rw [replacement_axiom]
      use i
    } ⟩,
    by {
      intro ⟨ x, hx ⟩
      rw [replacement_axiom] at hx
      obtain ⟨ i, hi ⟩ := hx
      use i
      simp [hi]
    } ⟩,
    by {
      intro i
      simp
      exact Subtype.property _
    } ⟩
  unfold tuple_equiv
  simp [hf]

theorem tuple_equiv_injective (n:ℕ) (X: SetTheory.Set.Fin n → Set) : Function.Injective (tuple_equiv n X) := by
  intro ⟨ t1, ht1 ⟩ ⟨ t2, ht2 ⟩ h
  simp
  rw [SetTheory.Set.Tuple.eq]
  intro i
  unfold tuple_equiv at h
  simp at h
  rw [funext_iff] at h
  specialize h i
  simp at h
  exact h

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  -- t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x
  -- Given a Tuple, construct a tuple function that just calls the Tuple x function.
  toFun := Function.surjInv (tuple_equiv_surjective n X)
  invFun := tuple_equiv n X
  left_inv := by {
    change Function.RightInverse (Function.surjInv (tuple_equiv_surjective n X)) (tuple_equiv n X)
    apply Function.rightInverse_surjInv
  }
  right_inv := by {
    change Function.LeftInverse (Function.surjInv (tuple_equiv_surjective n X)) (tuple_equiv n X)
    apply Function.leftInverse_surjInv
    constructor
    . exact tuple_equiv_injective n X
    . exact tuple_equiv_surjective n X
  }

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  rw [OrderedPair.eq]
  constructor <;> rfl

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  constructor <;> intro h <;> rw [OrderedPair.eq] at * <;> tauto

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  rw [OrderedPair.eq] at *
  constructor
  . rw [hpq.1, hqr.1]
  . rw [hpq.2, hqr.2]

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by
  rw [tuple_inj]

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
  rw [tuple_inj, tuple_inj]
  tauto

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
  rw [tuple_inj] at *
  rw [hab, hbc]

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  ext p
  constructor <;> intro h
  . rw [mem_union]
    rw [mem_cartesian, mem_cartesian] at *
    obtain ⟨ x, ⟨ y, hy ⟩, h ⟩ := h
    simp at hy
    obtain hy | hy := hy
    . left
      use x, ⟨ y, hy ⟩
    . right
      use x, ⟨ y, hy ⟩
  . rw [mem_union] at h
    rw [mem_cartesian, mem_cartesian] at *
    obtain h | h := h <;> obtain ⟨ x, ⟨ y, hy ⟩, h ⟩ := h <;> use x, ⟨ y, by simp [hy] ⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext p
  rw [mem_inter, mem_cartesian, mem_cartesian, mem_cartesian]
  constructor <;> intro h
  . obtain ⟨ x, ⟨ y, hy ⟩, _ ⟩ := h
    simp at hy
    constructor <;> use x, ⟨ y, by simp [hy] ⟩
  . obtain ⟨ hB, hC ⟩ := h
    obtain ⟨ ⟨ x1, hx1 ⟩, ⟨ y1, hy1 ⟩, h1 ⟩ := hB
    obtain ⟨ ⟨ x2, hx2 ⟩, ⟨ y2, hy2 ⟩, h2 ⟩ := hC
    rw [h1] at h2
    simp at h2
    obtain ⟨ hx, hy ⟩ := h2
    use ⟨ x1, by simp [hx, hx2] ⟩, ⟨ y1, by {
      simp
      use hy1
      simp [hy, hy2]
    } ⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  ext p
  rw [mem_sdiff, mem_cartesian, mem_cartesian, mem_cartesian]
  constructor <;> intro h
  . obtain ⟨ x, ⟨ y, hy ⟩, h ⟩ := h
    simp at hy
    constructor
    . use x, ⟨ y, by simp [hy] ⟩
    . intro contra
      obtain ⟨ _, ⟨ y1, hy1 ⟩, h2 ⟩ := contra
      rw [h2] at h
      simp at h
      rw [h.2] at hy1
      tauto
  . obtain ⟨ hB, hC ⟩ := h
    obtain ⟨ x, ⟨ y, hy ⟩, h ⟩ := hB
    by_cases hyC : y ∈ C
    . contrapose! hC
      use x, ⟨ y, by simp [hyC] ⟩
    . use x, ⟨ y, by simp [hy, hyC] ⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by aesop

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  ext p
  rw [mem_inter, mem_cartesian, mem_cartesian, mem_cartesian]
  constructor <;> intro h
  . obtain ⟨ hAB, hCD ⟩ := h
    obtain ⟨ ⟨ x1, hx1 ⟩, ⟨ y1, hy1 ⟩, hAB ⟩ := hAB
    obtain ⟨ ⟨ x2, hx2 ⟩, ⟨ y2, hy2 ⟩, hCD ⟩ := hCD
    rw [hAB] at hCD
    simp at hCD
    use ⟨ x1, by {
      simp [hx1]
      simp [hCD.1, hx2]
    } ⟩
    use ⟨ y1, by {
      simp [hy1]
      simp [hCD, hy2]
    } ⟩
  . obtain ⟨ ⟨ x, hx ⟩, ⟨ y, hy ⟩, h ⟩ := h
    simp at hx
    simp at hy
    constructor <;> use ⟨ x, by simp [hx] ⟩, ⟨ y, by simp [hy] ⟩

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {1}, ∅, ∅, {2}
  simp [SetTheory.Set.ext_iff] -- Wow that's crazy.

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use {1}, {2}, {1}, {3}
  simp [SetTheory.Set.ext_iff] -- Wow that's crazy.

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (_hC: C ≠ ∅) (_hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
  constructor <;> intro h
  . rw [subset_def] at h
    constructor <;> rw [subset_def]
    . intro a hA
      replace hB := nonempty_def hB
      obtain ⟨ b, hB ⟩ := hB
      specialize h (⟨ a, b ⟩:OrderedPair) (by {
        rw [mem_cartesian]
        use ⟨ a, hA ⟩, ⟨ b, hB ⟩
      })
      rw [mem_cartesian] at h
      obtain ⟨ ⟨ c, hC ⟩, _, h ⟩ := h
      simp at h
      simp [h, hC]
    . intro b hB
      replace hA := nonempty_def hA
      obtain ⟨ a, hA ⟩ := hA
      specialize h (⟨ a, b ⟩:OrderedPair) (by {
        rw [mem_cartesian]
        use ⟨ a, hA ⟩, ⟨ b, hB ⟩
      })
      rw [mem_cartesian] at h
      obtain ⟨ _, ⟨ d, hD ⟩, h ⟩ := h
      simp at h
      simp [h, hD]
  . obtain ⟨ hAC, hBD ⟩ := h
    rw [subset_def]
    intro p hp
    rw [mem_cartesian] at *
    obtain ⟨ ⟨ a, hA ⟩, ⟨ b, hB ⟩, h ⟩ := hp
    specialize hAC a hA
    specialize hBD b hB
    use ⟨ a, hAC ⟩, ⟨ b, hBD ⟩

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use ∅, {1}, {2}, {3}
  simp [subset_def]

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
  -- Use the function that returns pair (f z, g z)
  set h := fun z:Z ↦ mk_cartesian (f z) (g z)
  use h
  constructor
  . unfold h
    simp
    constructor <;> rw [funext_iff] <;> intro z <;> simp
  . intro h' ⟨ hf, hg ⟩
    unfold h
    rw [funext_iff] at *
    intro z
    specialize hf z
    specialize hg z
    simp at hf hg
    calc
      h' z = mk_cartesian (fst (h' z)) (snd (h' z)) := by simp
      _ = mk_cartesian (f z) (g z) := by rw [hg, hf]

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
  constructor <;> intro h
  . -- Already proven using induction earlier...
    contrapose! h
    exact finite_choice h
  . obtain ⟨ i, hi ⟩ := h
    -- Assume the contrary that there is a member. The tuple function value at i will be in empty set.
    by_contra hprod
    rw [SetTheory.Set.ext_iff] at hprod
    push_neg at hprod
    obtain ⟨ t, ht ⟩ := hprod
    rw [mem_iProd] at ht
    simp at ht
    obtain ⟨ f, _ ⟩ := ht
    have contra := (f i).2
    rw [SetTheory.Set.ext_iff] at hi
    specialize hi (f i)
    simp [contra] at hi

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
  ext x
  rw [mem_inter, mem_iUnion, mem_iUnion, mem_iUnion]
  constructor <;> intro h
  . obtain ⟨ ⟨ i, hA ⟩, ⟨ j, hB ⟩ ⟩ := h
    use mk_cartesian i j
    simp
    tauto
  . obtain ⟨ ⟨ p, hp ⟩, hx ⟩ := h
    simp at hx
    rw [mem_cartesian] at hp
    obtain ⟨ i, j, h ⟩ := hp
    simp [h] at hx
    constructor
    . use i
      tauto
    . use j
      tauto

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by
  constructor <;> intro h
  . ext x
    rw [SetTheory.Set.ext_iff] at h
    set p := mk_cartesian x (f x)
    specialize h p
    unfold graph at h
    rw [specification_axiom', specification_axiom'] at h
    simp at h
    exact (congrArg Subtype.val h).symm
  . ext p
    unfold graph
    rw [specification_axiom'', specification_axiom'']
    rw [funext_iff] at h
    constructor <;> intro hp <;> obtain ⟨ hp, hfp ⟩ := hp <;> use hp <;> rw [← hfp] <;>
      specialize h (fst ⟨p, hp⟩) <;> simp [h]

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by
  -- Create f using hvert's y value.
  set f := fun x:X ↦ (((hvert x).choose):Y)
  use f
  have hf : G = graph f
  . ext p
    unfold graph
    unfold f
    rw [specification_axiom'']
    constructor <;> intro h
    . use (by exact hG p h)
      set c := hvert (fst ⟨p, hG p h⟩)
      have hc := c.choose_spec
      obtain ⟨ hc1, hc2 ⟩ := hc
      symm
      apply hc2
      -- We need to split up p...
      have hp := hG p h
      have hp2 := hp
      rw [mem_cartesian] at hp
      obtain ⟨ x, y, hp ⟩ := hp
      rw [hp] at h
      have : ⟨ p, hp2 ⟩ = mk_cartesian x y
      . unfold mk_cartesian
        simp [hp]
      rw [this]
      simp [h]
    . obtain ⟨ hp, h ⟩ := h
      set c := hvert (fst ⟨p, hp⟩)
      have hc := c.choose_spec
      obtain ⟨ hc1, hc2 ⟩ := hc
      rw [h] at hc1
      suffices this : p = (⟨ fst ⟨p, hp⟩, snd ⟨p, hp⟩ ⟩:OrderedPair)
      . rw [this]
        exact hc1
      rw [mem_cartesian] at hp
      obtain ⟨ x, y, h ⟩ := hp
      simp [h]
  constructor
  . simp
    exact hf
  . intro f' h
    ext x
    -- Since we know both graph f/f' = G, then we can use hvert to assert their y values are equal.
    unfold graph at h
    rw [SetTheory.Set.ext_iff] at h hf
    specialize h (⟨ x, f' x ⟩:OrderedPair)
    specialize hf (⟨ x, f x ⟩:OrderedPair)
    replace h := h.mpr (by {
      rw [specification_axiom'']
      simp
    })
    replace hf := hf.mpr (by {
      rw [specification_axiom'']
      simp
    })
    specialize hvert x
    obtain ⟨ y, _, hy ⟩ := hvert
    have h1 := hy (f' x) (by simp [h])
    have h2 := hy (f x) (by simp [hf])
    rw [h1, h2]

-- ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X
#check SetTheory.Set.exists_powerset

/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
  -- Y*X = {(y1,x1), (y2,x2)...} (all possible y -> x mappings)
  -- Taking the powerset results in each element containing some subset of these mappings.
  -- This is only a valid function if each y has exactly one element.
  -- So take powerset of Y*X, then replace with a function that satisfies graph equality.
  set S:Set := (exists_powerset (Y ×ˢ X)).choose.replace
    (P := fun S' F ↦ ∃ f: Y → X, f = F ∧ S'.val = graph f) (by {
    -- Prove S' can't have multiple satisfying F's.
    -- If f1/f2 satisfies, then S' = graph f1/f2 and then we can use injectivity.
    intro S'
    intro F1 F2 ⟨ hF1, hF2 ⟩
    simp at hF1 hF2
    obtain ⟨ f1, hf1, hf1S ⟩ := hF1
    obtain ⟨ f2, hf2, hf2S ⟩ := hF2
    rw [hf1S] at hf2S
    simp [graph_inj] at hf2S
    rw [← hf1, ← hf2, hf2S]
  })
  have goal : ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F
  . intro F
    unfold S
    set c := exists_powerset (Y ×ˢ X)
    have hc := c.choose_spec
    constructor <;> intro h
    . rw [replacement_axiom] at h
      tauto
    . obtain ⟨ f, hf ⟩ := h
      rw [replacement_axiom]
      use ⟨ graph f, by {
        specialize hc (graph f)
        rw [hc]
        use graph f, rfl
        unfold graph
        exact specify_subset fun p ↦ f (fst p) = snd p
      } ⟩
      use f
  apply ExistsUnique.intro S
  . exact goal
  . intro S' hS'
    ext f
    specialize goal f
    specialize hS' f
    tauto

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    -- Prove for Fin n for all n.
    -- Then define a function that instantiates the exist with a choose.
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
  have h_bounded : ∀ n': ℕ, ∃ a: Fin (n'+1) → X, a ⟨ 0, by {
    rw [mem_Fin]
    use 0
    simp
    rfl
  } ⟩ = c ∧ ∀ n, (hi: n < n') → a ⟨ (n + 1:ℕ), by {
    rw [mem_Fin]
    use n+1
    simp [hi]
  } ⟩ = f n (a ⟨ n, by {
    rw [mem_Fin]
    use n
    simp
    linarith
  } ⟩)
  . intro n
    induction' n with i IH
    . use fun _ ↦ c
      simp
    obtain ⟨ a, ha, ha2 ⟩ := IH
    use fun n ↦ if hn: n ≤ i then a (⟨ n, sorry ⟩) else f sorry (a (⟨ sorry, sorry ⟩))
    sorry
  set a: nat → X := fun n ↦ (h_bounded (n+5)).choose ⟨ n, by {
    rw [mem_Fin]
    use n
    simp
    linarith
  } ⟩
  have ha : a 0 = c ∧ ∀ (n : ℕ), a ↑(n + 1) = f (↑n) (a ↑n)
  . constructor
    . unfold a
      set c := h_bounded (nat_equiv.symm 0 + 5)
      have hc := c.choose_spec
      tauto
    intro n
    unfold a
    set c := h_bounded (nat_equiv.symm ↑(n + 1) + 5)
    set d := h_bounded (nat_equiv.symm ↑(n) + 5)
    have hc := c.choose_spec.2
    have hc2 := hc n (by sorry)
    simp [hc2]
    have helper : ∀ n', (hn: n' ≤ n) → c.choose ⟨ n', by sorry ⟩ = d.choose ⟨ n', by sorry ⟩
    . intro n'
      induction' n' with i hi
      . sorry
      sorry
    specialize helper n (by linarith)
    rw [helper]
  apply ExistsUnique.intro a
  . exact ha
  . intro a' ha'
    ext n
    induction' hx1: (n:ℕ) with i hi generalizing n
    . sorry
    sorry

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, ⟨ hf, hf2 ⟩, hf3⟩ := recursion nat' (fun _ n ↦ succ n) zero
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · have hx1 := nat_coe_eq_zero hx1
          rw [hx1]
          rw [hx1, hf] at heq
          match hn:(x2:ℕ) with
          | 0 => {
            have hn := nat_coe_eq_zero hn
            simp [hn]
          }
          | n + 1 => {
            specialize hf2 n
            have : ↑(n + 1) = x2
            . exact
              Eq.symm
                ((fun [SetTheory] n m ↦ (nat_equiv_symm_inj n m).mp) x2 (↑(n + 1))
                  (congrArg (⇑nat_equiv.symm) (nat_coe_eq hn)))
            rw [this, ← heq] at hf2
            specialize succ_ne (f ↑n)
            simp [hf2] at succ_ne
          }
        sorry
      sorry
    sorry
  sorry


end Chapter3
