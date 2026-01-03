import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  rw [succ_add, succ_toNat, hn, succ_toNat]
  ring

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  . rw [show zero = 0 from rfl, zero_mul, _root_.Nat.zero_mul]
  rw [succ_mul, map_add, hn, succ_toNat]
  ring

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  . contrapose!
    intro h
    obtain ⟨ ⟨ d, hd ⟩, h2 ⟩ := h
    -- Can't find Mathlib theorem to prove < with le and ne...
    rw [Nat.lt_iff_add_one_le]
    match d with
    | 0 => {
      rw [add_zero] at hd
      rw [hd] at h2
      contradiction
    }
    | succ d => {
      rw [le_iff_exists_add]
      use d.toNat
      rw [hd, map_add, succ_toNat]
      ring
    }
  . intro h
    obtain ⟨ d, hd ⟩ := h
    rw [le_iff_exists_add]
    use d.toNat
    rw [← map_add]
    rw [hd]

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m hm
  . rw [show zero = 0 from rfl, pow_zero, zero_toNat]
    ring
  rw [succ_toNat, pow_succ, map_mul, ← hm]
  ring


/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  unfold Function.Injective
  intro a1
  induction' a1 with a1 ih
  . intro a h
    match a with
    | 0 => rfl
    | n + 1 => {
      unfold natCast at h
      have := (P.succ_ne (P.natCast n)).symm
      contradiction
    }
  intro a2 h
  match a2 with
  | 0 => {
    unfold natCast at h
    have := P.succ_ne (P.natCast a1)
    contradiction
  }
  | a2 + 1 => {
    apply P.succ_cancel at h
    specialize ih h
    rw [ih]
  }

/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective
  intro b
  -- (fun b ↦ ∃ a, P.natCast a = b)
  have h : (∃ a, P.natCast a = P.zero)
  . use 0
  replace h := P.induction (fun b ↦ ∃ a, P.natCast a = b) h
  simp at h
  apply h
  intro a
  use a.succ

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by {
    have h := equiv.equiv_zero
    rw [Equiv.symm_apply_eq equiv.1]
    exact h.symm
  }
  equiv_succ q := by {
    have h := equiv.equiv_succ
    rw [Equiv.symm_apply_eq equiv.1]
    specialize h (Equiv.equiv.symm q)
    rw [h]
    simp
  }

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by {
    simp
    have hpq := equiv1.equiv_zero
    have hqr := equiv2.equiv_zero
    rw [hpq, hqr]
  }
  equiv_succ p := by {
    simp
    have hpq := equiv1.equiv_succ
    have hqr := equiv2.equiv_succ
    specialize hqr (equiv p)
    rw [← hqr]; clear hqr
    specialize hpq p
    rw [hpq]
  }

#check Function.surjInv
#check Function.invFun

/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := Function.surjInv (natCast_surjective P)
    left_inv := by {
      apply Function.leftInverse_surjInv
      constructor
      . exact natCast_injective P
      . exact natCast_surjective P
    }
    right_inv := by {
      apply Function.rightInverse_surjInv
    }
  }
  equiv_zero := by {
    simp
    rfl
  }
  equiv_succ n := by {
    simp
    rfl
  }

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by
  have h1 := Equiv.symm (Equiv.fromNat P)
  have h2 := Equiv.fromNat Q
  exact Equiv.trans h1 h2

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  exact P.induction (fun n ↦ equiv1 n = equiv2 n) (by {
    simp [equiv_zero1, equiv_zero2]
  }) (by {
    simp
    intro i IH
    simp [equiv_succ1, equiv_succ2, IH]
  }) n

noncomputable abbrev nat_recurse_internal {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) (n: ℕ) : ℕ :=
  let e := Equiv.symm (Equiv.fromNat P);
  match n with
    | 0 => e.equiv c
    | n + 1 => e.equiv (f (e.equiv.symm n) (e.equiv.symm (nat_recurse_internal f c n)))

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  -- I don't think it's possible to define a function using PeanoAxioms...
  -- But we can convert to Mathlib_Nat and use its natural recursion before converting back.
  apply existsUnique_of_exists_of_unique
  . set e := Equiv.symm (Equiv.fromNat P)
    use fun x ↦ e.equiv.symm (nat_recurse_internal f c (e.equiv x))
    simp
    constructor
    . unfold nat_recurse_internal
      simp [Equiv.equiv_zero]
      simp [Mathlib_Nat]
    intro n
    conv => lhs; unfold nat_recurse_internal
    simp [Equiv.equiv_succ]
    simp [Mathlib_Nat]
  . intro f1 f2 ⟨ hf1z, hf1s ⟩ ⟨ hf2z, hf2s ⟩
    ext x
    have := P.induction (fun x ↦ f1 x = f2 x) (by {
      simp [hf1z, hf2z]
    }) (by {
      simp
      intro x hx
      simp [hf1s, hf2s, hx]
    }) x
    exact this

end PeanoAxioms
