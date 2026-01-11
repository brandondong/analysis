import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  use fun n ↦ ⟨ ((n:ℕ) + (n:ℕ)), by {
    rw [specification_axiom'']
    simp
    exact Subtype.property _
  } ⟩
  constructor
  . intro n1 n2 h
    simp at h
    have : nat_equiv.symm n1 = nat_equiv.symm n2
    . linarith
    exact (nat_equiv_symm_inj n1 n2).mp this
  . intro ⟨ y, hy ⟩
    rw [specification_axiom''] at hy
    obtain ⟨ hy, hy2 ⟩ := hy
    obtain ⟨ x, hx ⟩ := hy2
    use x
    simp
    rw [← hx]
    simp

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  use id
  exact Function.bijective_id

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨ f, hf ⟩ := h
  rw [Function.bijective_iff_has_inverse] at hf
  obtain ⟨ g, hgl, hgr ⟩ := hf
  use g
  use Function.LeftInverse.injective hgr, Function.RightInverse.surjective hgl

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨ f1, hf1i, hf1s ⟩ := h1
  obtain ⟨ f2, hf2i, hf2s ⟩ := h2
  use fun x ↦ f2 (f1 x)
  constructor
  . intro x1 x2 h
    simp at h
    specialize hf2i h
    exact hf1i hf2i
  . intro z
    specialize hf2s z
    obtain ⟨ y, hy ⟩ := hf2s
    specialize hf1s y
    obtain ⟨ x, hx ⟩ := hf1s
    use x
    simp [hx, hy]

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  rw [has_card_iff]
  -- Want to go the opposite way (Fin n -> [1, n] so we can use x+1).
  -- Proving this function is bijective is sufficient.
  change EqualCard _ _
  apply EqualCard.symm
  unfold EqualCard
  set f := fun i:Fin n ↦ (⟨ (i:ℕ) + (1:ℕ), by {
    rw [specification_axiom'']
    use Subtype.property _
    obtain ⟨ i, hi ⟩ := i
    simp
    rw [mem_Fin] at hi
    obtain ⟨ x, hx1, hx2 ⟩ := hi
    simp [hx2]
    simp_all
    linarith
  } ⟩ :(nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)))
  use f
  unfold f
  constructor
  . intro i1 i2 h
    simp at h
    simp [h]
  . intro ⟨ y, hy ⟩
    rw [specification_axiom''] at hy
    obtain ⟨ hy2, hy3, hy4 ⟩ := hy
    match hy':((⟨ y, hy2 ⟩:nat):ℕ) with
    | 0 => linarith
    | y' + 1 => {
      use ⟨ y', by {
        rw [mem_Fin]
        use y'
        simp
        linarith
      } ⟩
      simp at hy' ⊢
      have : y = ((y' + (1:ℕ)):Object)
      . rw [← hy']
        simp
      simp [this]
      apply Fin.toNat_mk
      linarith
    }

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hfi hfs using hX
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.
  have h := nonempty_def hnon
  obtain ⟨ i, hi ⟩ := h
  specialize hfs ⟨ i, hi ⟩
  obtain ⟨ ⟨ e, he ⟩, _ ⟩ := hfs
  simp [this] at he

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  rw [has_card_iff]
  constructor <;> intro h
  . obtain ⟨ f, hfi, hfs ⟩ := h
    -- Assume to the contrary X is nonempty. Then f X is part of Fin 0.
    by_contra h
    -- change X ≠ ∅ at h
    replace h := nonempty_def h
    obtain ⟨ x, hx ⟩ := h
    have h := (f ⟨ x, hx ⟩).2
    simp at h
  . set f:X → (Fin 0) := fun e ↦ ⟨ 1, by {
      have h2 := e.2
      simp [h] at h2
    } ⟩
    use f
    constructor
    . intro ⟨ e, he ⟩
      simp [h] at he
    . intro ⟨ e, he ⟩
      simp at he

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  have x_helper (x':X) (hx': ¬ x' = x) : x'.val ∈ X'
  . simp [X', coe_inj, hx']
    exact Subtype.property _
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g
  . obtain ⟨ hfi, hfs ⟩ := hf
    constructor
    . intro x1 x2 h
      -- f x != m0 due to injectivity.
      have fx_helper (x': X') : f (ι x') ≠ m₀
      . intro contra
        simp at hm₀f
        rw [← hm₀f, ← Fin.coe_inj] at contra
        specialize hfi contra
        have h := x'.2
        simp [X'] at h
        simp [ι] at hfi
        contrapose! h; intro _
        symm
        symm at hfi
        simp [hfi]
      -- Split on f x and consider both branches which are ultimately f x with/without subtraction.
      -- f is injective and so we can cancel that as long as we can prove f x is > 0 (f x > m0).
      -- Branch mismatch case (f x1 < m0, f x2 > m0) contradicts original assumption of equality of g.
      simp [g] at h
      have branch_helper (x1 x2 : X') (h1: (f (ι x1)) < m₀) (h2: ¬↑(f (ι x2)) < m₀) (h: ((f (ι x1)):ℕ) = ↑(f (ι x2)) - 1) : False
      . contrapose! h2
        have := fx_helper x2
        omega
      by_cases h1 : (f (ι x1)) < m₀ <;> by_cases h2 : (f (ι x2)) < m₀ <;> simp [h1, h2] at h
      . rw [← Fin.coe_inj] at h
        specialize hfi h
        simp [ι, coe_inj] at hfi
        exact hfi
      . have := branch_helper x1 x2 h1 h2 h
        contradiction
      . have := branch_helper x2 x1 h2 h1 h.symm
        tauto
      . simp at h1 h2
        have := fx_helper x1
        have := fx_helper x2
        have h : ((f (ι x1)):ℕ) = ↑(f (ι x2)) := by omega
        rw [← Fin.coe_inj] at h
        specialize hfi h
        simp [ι, coe_inj] at hfi
        exact hfi
    . intro y
      have hy : y.val ∈ (Fin n)
      . apply mem_Fin2
        omega
      by_cases hy2 : y < m₀
      . -- If y < m0, consider x' in X where f x' = y.
        specialize hfs ⟨ y, hy ⟩
        obtain ⟨ x', hx' ⟩ := hfs
        -- x' != x because f x = m0.
        have hx'2 : x'.val ∈ X'
        . apply x_helper
          intro contra
          rw [contra] at hx'
          simp [hx'] at hm₀f
          omega
        use ⟨ x', hx'2 ⟩
        unfold g
        have hx'f : f (ι ⟨ x', hx'2 ⟩) < m₀
        . simp [ι, hx', hy2]
        simp [hx'f]
        unfold ι
        simp [hx']
      . -- Otherwise y >= m0, consider x' in X where f x' = y + 1.
        simp at hy2
        set y' := (y:ℕ) + 1
        have hy' : (y':Object) ∈ (Fin (n))
        . apply mem_Fin3
          simp [y']
          have hy3 := y.2
          rw [mem_Fin] at hy3
          obtain ⟨ x, hx, hx2 ⟩ := hy3
          simp at hx2
          rw [hx2]
          omega
        specialize hfs ⟨ y', hy' ⟩
        obtain ⟨ x', hx' ⟩ := hfs
        unfold g
        -- x' != x because f x = m0 and f x' = y + 1 > m0.
        have hx'2 : x'.val ∈ X'
        . apply x_helper
          intro contra
          rw [contra] at hx'
          simp [hx', y'] at hm₀f
          omega
        use ⟨ x', hx'2 ⟩
        have hx'f : ¬ (f (ι ⟨ x', hx'2 ⟩) < m₀)
        . simp [ι, hx', fin_eq, y']
          omega
        simp [hx'f]
        unfold ι
        simp [hx']
        have : (⟨ y', hy' ⟩:(Fin n)) = y'
        . exact (Fin.coe_eq_iff ⟨↑y', hy'⟩).mp rfl
        simp [this, y']
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction' n with i IH
  . use 0
    intro ⟨ x, hx ⟩
    simp at hx
  -- Consider the function that maps to f for all i. Then this is bounded by M and so is f.
  -- f (i+1) might be higher so consider max(M, f (i+1)).
  set g : (Fin i) -> nat := fun x ↦ f ⟨ x, by {
    obtain ⟨ x, hx ⟩ := x
    rw [mem_Fin] at *
    obtain ⟨ x', hx', hx'2 ⟩ := hx
    use x'
    simp [hx'2]
    linarith
  } ⟩
  specialize IH g
  obtain ⟨ M, IH ⟩ := IH
  use max M ((f ⟨ i, by simp; exact Subtype.property _ ⟩):ℕ)
  intro n
  -- If n < i, f n = g n <= M.
  -- Otherwise f n <= f n.
  by_cases hn : n < i
  . have hn2 : n.val ∈ (Fin i)
    . rw [mem_Fin]
      use n
      simp [hn]
    specialize IH ⟨ n, hn2 ⟩
    have : f n = g ⟨ n, hn2 ⟩
    . unfold g
      simp
    rw [this]
    simp [IH]
  . have : n = ⟨ i, by simp; exact Subtype.property _ ⟩
    -- nat nonsense for what should be immediately obvious.
    . obtain ⟨ n, hn2 ⟩ := n
      rw [mem_Fin] at hn2
      obtain ⟨ x, hx, hx2 ⟩ := hn2
      simp
      simp at hn
      simp [hx2]
      simp [hx2] at hn
      have : i ≤ x
      . simp_all
      linarith
    simp [this]

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  rw [← has_card_zero]
  constructor <;> intro h
  . constructor
    . use 0
    . exact has_card_to_card h
  . obtain ⟨ hf, hc ⟩ := h
    have hc2 := has_card_card hf
    rwa [hc] at hc2

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

open Classical in
/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  -- There exists a bijection from X -> Fin n.
  -- We can create a new bijection from X' -> Fin n+1 by mapping x to n.
  set X' := (X ∪ {x})
  obtain ⟨ n, hX ⟩ := hX
  have hX2 := hX
  rw [has_card_iff] at hX
  obtain ⟨ f, hfi, hfj ⟩ := hX
  have goal : X'.has_card (n+1)
  . set g: X' → Fin (n+1) := fun x ↦ if hx:(x.val ∈ X) then ⟨ f ⟨ x, hx ⟩, by {
      set fx := (f ⟨↑x, hx⟩)
      have hfx := fx.property
      rw [mem_Fin] at *
      obtain ⟨ x, hx, hx2 ⟩ := hfx
      use x
      simp [hx2]
      linarith
    } ⟩ else Fin_mk (n+1) n (by linarith)
    -- Useful helpers for later.
    have hX_iff' : ∀ x' ∈ X, x' ∈ X'
    . intro x' hx'
      unfold X'
      simp [hx']
    have hxX' : x ∈ X'
    . unfold X'
      simp
    have x_iff : ∀ x' ∈ X', x' ≠ x → x' ∈ X
    . intro x' hx' hx
      unfold X' at hx'
      simp at hx'
      tauto
    have g_iff : ∀ x', (hx:x' ∈ X') → g ⟨ x', hx ⟩ = n ↔ x' = x
    . intro x' hx'
      constructor <;> intro h
      . by_contra hx
        specialize x_iff x' hx' hx
        unfold g at h
        simp [x_iff] at h
        set contra := (f ⟨ x', of_eq_true (eq_true x_iff) ⟩)
        have hc := contra.2
        rw [mem_Fin] at hc
        obtain ⟨ m, hm ⟩ := hc
        simp at hm
        linarith
      . simp [h]
        unfold g
        simp [hx]
    use g
    constructor
    . intro x1 x2 h
      -- If g x' = n, then we assert x' = x.
      -- Otherwise g x' != n and so x1 and x2 != x.
      -- Then g = f which is injective.
      by_cases hg : (g x1) = n
      . have h1 := (g_iff x1 x1.2).mp hg
        rw [h] at hg
        have h2 := (g_iff x2 x2.2).mp hg
        rw [← h2, coe_inj] at h1
        exact h1
      . have hg2 := hg
        rw [h] at hg2
        have h1 := g_iff x1 x1.2
        simp [hg] at h1
        have h2 := g_iff x2 x2.2
        simp [hg2] at h2
        have h3 := x_iff x1 x1.2 h1
        have h4 := x_iff x2 x2.2 h2
        unfold g at h
        simp [h3, h4] at h
        rw [coe_inj] at h
        specialize hfi h
        simp at hfi
        rwa [coe_inj] at hfi
    . intro y
      -- if y = n, then use x.
      -- Otherwise y < n and so we can use surjectivity of f.
      by_cases hy : y = n
      . use ⟨ x, hxX' ⟩
        unfold g
        simp [hx]
        exact hy.symm
      . have hy2 : y.val ∈ (Fin n)
        . have hy2 := y.2
          rw [mem_Fin] at *
          obtain ⟨ x, hx, hx2 ⟩ := hy2
          use x
          simp [hx2]
          simp at hx2
          rw [hx2] at hy
          change x ≠ n at hy
          omega
        specialize hfj ⟨ y, hy2 ⟩
        obtain ⟨ x', hx' ⟩ := hfj
        have hx'2 : x'.val ∈ X' := hX_iff' x' x'.2
        use ⟨ x', hx'2 ⟩
        unfold g
        simp [Subtype.property, hx']
  constructor
  . use n+1
  . have h1 := has_card_to_card goal
    have h2 := has_card_to_card hX2
    simp [h1, h2]

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  -- Induct on the cardinality of X, generalizing X.
  obtain ⟨ i, hi ⟩ := hX
  obtain ⟨ j, hj ⟩ := hY
  revert X
  induction' i with i IH
  . intro X hX
    have he : X = ∅ := by exact has_card_zero.mp hX
    have : X ∪ Y = Y
    . ext x
      simp [he]
    rw [this]
    constructor
    . use j
    . linarith
  intro X hX
  -- IH is for all sets of X size i, the property holds. Prove for X of size i+1.
  -- We can consider erasure of x and use IH to show it holds.
  have he : X ≠ ∅
  . intro contra
    have : X.card = i+1 := by exact has_card_to_card hX
    have : X.card = 0 := by exact card_eq_zero_of_empty contra
    linarith
  replace he := nonempty_def he
  obtain ⟨ x, hx ⟩ := he
  set X' := X \ {x}
  have hX' : X'.has_card i
  . have := card_erase (by linarith) hX ⟨ x, hx ⟩
    simp at this
    exact this
  have hXc : X.card = i+1 := by exact has_card_to_card hX
  have hYc : Y.card = j := by exact has_card_to_card hj
  have hX'c : X'.card = i := by exact has_card_to_card hX'
  specialize IH hX'
  -- Then either x is in X' or Y or not.
  by_cases hx2 : x ∈ ((X' ∪ Y))
  . -- If it is, then X' or Y = X or Y and we're done.
    have he : (X' ∪ Y) = (X ∪ Y)
    . ext x'
      simp [X']
      by_cases hx' : x' = x <;> simp [hx']
      simp [X'] at hx2
      simp [hx2]
    rw [← he]
    use IH.1
    linarith
  -- Otherwise, we can use card_insert to get the relation.
  have h_ins := card_insert IH.1 hx2
  have he : X' ∪ Y ∪ {x} = X ∪ Y
  . ext x'
    simp [X']
    by_cases hx' : x' = x <;> simp [hx']
    . tauto
  rw [← he, h_ins.2]
  use h_ins.1
  linarith

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  -- Induct on cardinality of X, generalizing X.
  obtain ⟨ i, hi ⟩ := hX
  obtain ⟨ j, hj ⟩ := hY
  revert X
  induction' i with i IH
  . intro X hXd hX
    have he : X = ∅ := by exact has_card_zero.mp hX
    have : X ∪ Y = Y
    . ext x
      simp [he]
    rw [this]
    have : X.card = 0 := by exact card_eq_zero_of_empty he
    simp [this]
  intro X hXd hX
  -- IH is for all sets of X size i, the property holds. Prove for X of size i+1.
  -- We can consider erasure of x and use IH to show it holds.
  have he : X ≠ ∅
  . intro contra
    have : X.card = i+1 := by exact has_card_to_card hX
    have : X.card = 0 := by exact card_eq_zero_of_empty contra
    linarith
  replace he := nonempty_def he
  obtain ⟨ x, hx ⟩ := he
  set X' := X \ {x}
  have hX' : X'.has_card i
  . have := card_erase (by linarith) hX ⟨ x, hx ⟩
    simp at this
    exact this
  have hXc : X.card = i+1 := by exact has_card_to_card hX
  have hYc : Y.card = j := by exact has_card_to_card hj
  have hX'c : X'.card = i := by exact has_card_to_card hX'
  have hX'd : Disjoint X' Y
  . simp [disjoint_iff, SetTheory.Set.ext_iff] at hXd ⊢
    intro x hx
    have hx2 : x ∈ X
    . simp [X'] at hx
      tauto
    exact hXd x hx2
  specialize IH hX'd hX'
  -- Then x is not in X' or Y so we can use card_insert to get the relation.
  have hX'f : (X' ∪ Y).finite
  . have h1 : X'.finite := by use i
    have h2 : Y.finite := by use j
    exact (card_union h1 h2).1
  have hx2 : x ∉ (X' ∪ Y)
  . intro contra
    simp at contra
    rw [disjoint_iff] at hXd
    simp [SetTheory.Set.ext_iff] at hXd
    specialize hXd x hx
    obtain contra | contra := contra
    . simp [X'] at contra
    . contradiction
  have h_ins := (card_insert hX'f hx2).2
  have he : X' ∪ Y ∪ {x} = X ∪ Y
  . ext x'
    simp [X']
    by_cases hx' : x' = x <;> simp [hx']
    . tauto
  rw [← he, h_ins]
  linarith

#check SetTheory.Set.card_erase

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  obtain ⟨ n, hn ⟩ := hX
  revert X Y
  -- Induct on the cardinality of X.
  -- IH is for all sets of X size i, the subset relation holds. Prove for X of size i+1.
  induction' n with i IH
  . intro X Y hY hX
    have hX2 : X = ∅ := by exact has_card_zero.mp hX
    have hY2 : Y = ∅ := by {
      ext y
      simp
      intro hy
      have hy2 := hY y hy
      simp [hX2] at hy2
    }
    have hY3 : Y.has_card 0 := by exact has_card_zero.mpr hY2
    constructor
    . use 0
    have hY4 : Y.card = 0 := by exact card_eq_zero_of_empty hY2
    have hX3 : X.card = 0 := by exact card_eq_zero_of_empty hX2
    simp [hY4, hX3]
  intro X Y hYX hX
  -- Consider Y-y and X-y in IH (case where Y is empty is trivial).
  -- Then use card_insert on that result to get relation of X/Y.
  by_cases hY : Y = ∅
  . have hY2 : Y.has_card 0 := by exact has_card_zero.mpr hY
    constructor
    . use 0
    have hY3 : Y.card = 0 := by exact card_eq_zero_of_empty hY
    have hX2 : X.card = (i + 1) := by exact has_card_to_card hX
    simp [hY3]
  have h := nonempty_def hY
  obtain ⟨ y, hyY ⟩ := h
  have hyX := hYX y hyY
  set X' := X \ {y}
  set Y' := Y \ {y}
  have hY'X' : Y' ⊆ X' := by {
    unfold Y' X'
    intro y' hy'
    simp at *
    constructor
    . exact hYX y' hy'.1
    . tauto
  }
  have hX' : X'.has_card i
  . have hi : i+1 ≥ 1 := by linarith
    have he := SetTheory.Set.card_erase hi hX ⟨ y, hyX ⟩
    simp at he
    exact he
  specialize IH hY'X' hX'
  obtain ⟨ IH, hY'2 ⟩ := IH
  have hY'f := IH
  obtain ⟨ j, hY'3 ⟩ := IH
  have hY'4 : Y'.card = j := by exact has_card_to_card hY'3
  have hyY' : y ∉ Y' := by {
    unfold Y'
    simp
  }
  have hY'Y : Y' ∪ {y} = Y := by {
    unfold Y'
    ext y'
    simp
    by_cases hy' : y' = y
    . simp [hy', hyY]
    . simp [hy']
  }
  have hY2 : Y.has_card (j+1)
  . have hIns := card_insert hY'f hyY'
    rw [hY'Y, hY'4] at hIns
    have h := has_card_card hIns.1
    rwa [hIns.2] at h
  constructor
  . use j+1
  have hY3 : Y.card = (j+1) := by exact has_card_to_card hY2
  have hX2 : X.card = i+1 := by exact has_card_to_card hX
  have hX'2 : X'.card = i := by exact has_card_to_card hX'
  simp [hY'4, hX'2] at hY'2
  simp [hY3, hX2, hY'2]

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  obtain ⟨ n, hn ⟩ := hX
  revert X Y
  -- Induct on the cardinality of X.
  induction' n with i IH
  . intro X Y hYX hX
    have : X = ∅ := by exact has_card_zero.mp hX
    simp [this] at hYX
    obtain ⟨ h1, h2 ⟩ := hYX
    contrapose! h2
    ext y
    simp
    intro h
    have := h1 y h
    simp at this
  intro X Y hYX hX
  -- IH is for all sets of X size i, the subset relation holds. Prove for X of size i+1.
  -- Consider Y-y and X-y in IH (case where Y is empty is trivial).
  have hXc : X.card = i+1 := by exact has_card_to_card hX
  by_cases hY : Y = ∅
  . have : Y.card = 0 := by exact card_eq_zero_of_empty hY
    linarith
  have h := nonempty_def hY
  obtain ⟨ y, hyY ⟩ := h
  have hyX : y ∈ X
  . exact hYX.1 y hyY
  set X' := X \ {y}
  set Y' := Y \ {y}
  have hY'X' : Y' ⊂ X'
  . obtain ⟨ h1, h2 ⟩ := hYX
    simp [Y', X']
    constructor
    . intro y' hy'
      simp at hy' ⊢
      constructor
      . exact h1 y' hy'.1
      . tauto
    . contrapose! h2
      simp [SetTheory.Set.ext_iff] at h2 ⊢
      intro x
      specialize h2 x
      by_cases h : x = y
      . simp [h]
        tauto
      . tauto
  have hX' : X'.has_card i
  . have hi : i+1 ≥ 1 := by linarith
    have he := SetTheory.Set.card_erase hi hX ⟨ y, hyX ⟩
    simp at he
    exact he
  specialize IH hY'X' hX'
  have hX'f : X'.finite := by (use i)
  have hY'f : Y'.finite
  . exact (card_subset hX'f hY'X'.1).1
  have hY'f2 := hY'f
  obtain ⟨ j, hY' ⟩ := hY'f2
  have hY'c : Y'.card = j := by exact has_card_to_card hY'
  have hX'c : X'.card = i := by exact has_card_to_card hX'
  have hyY' : y ∉ Y' := by {
    unfold Y'
    simp
  }
  have hY'Y : Y' ∪ {y} = Y := by {
    unfold Y'
    ext y'
    simp
    by_cases hy' : y' = y
    . simp [hy', hyY]
    . simp [hy']
  }
  -- Then use card_insert on that result to get relation of X/Y.
  have hY2 : Y.card = (j+1)
  . have hIns := (card_insert (hY'f) hyY').2
    rwa [hY'Y, hY'c] at hIns
  linarith

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  -- Induction on cardinality of X.
  obtain ⟨ n, hX ⟩ := hX
  revert X
  induction' n with i IH
  . intro X f hX
    have : (image f X) = ∅
    . have hXe : X = ∅ := by exact has_card_zero.mp hX
      ext x
      simp [hXe]
    simp [this]
  intro X f hX
  -- IH: Assume holds for all X of size n, prove for set of size n+1.
  -- Consider X' = X \ {x}. We can create f' off of f.
  have hXc : X.card = i + 1 := by exact has_card_to_card hX
  have hXe : X ≠ ∅
  . intro contra
    have : X.card = 0 := by exact card_eq_zero_of_empty contra
    omega
  obtain ⟨ x, hx ⟩ := nonempty_def hXe
  set X' := X \ {x}
  have hX' : X'.has_card i
  . have := card_erase (by omega) hX ⟨ x, hx ⟩
    simp at this
    simp [X', this]
  have hX'c : X'.card = i := by exact has_card_to_card hX'
  set f':X' → Y := fun x ↦ f ⟨ x, by {
    have hx := x.2
    simp [X'] at hx
    tauto
  } ⟩
  -- From IH, |image f' X'| <= |X'|
  specialize IH f' hX'
  -- No matter what f x is, relation will still hold for f and X.
  by_cases h : (f ⟨ x, hx ⟩).val ∈ image f' X'
  . -- Case 1: f x is already in image f' X'. Then the two images are equal.
    have : image f X = image f' X'
    . ext y
      constructor <;> intro hy
      . simp at hy
        obtain ⟨ x', ⟨ hx', hfx' ⟩ ⟩ := hy
        by_cases hx'2 : x' = x
        . simp only [← hx'2, hfx'] at h
          exact h
        . simp
          use x', (by simp [X']; tauto)
      . simp at hy ⊢
        obtain ⟨ x', ⟨ hx', hfx' ⟩ ⟩ := hy
        use x', (by simp [X'] at hx'; tauto)
    simp [this]
    use IH.1
    omega
  . -- Case 2: Use card_insert.
    have h_ins := card_insert IH.1 h
    have : image f X = (image f' X' ∪ {↑(f ⟨x, hx⟩)})
    . ext y
      constructor <;> intro hy
      . simp at hy
        obtain ⟨ x', ⟨ hx', hfx' ⟩ ⟩ := hy
        simp
        by_cases hx'2 : x' = x
        . right
          simp [← hx'2, hfx']
        . left
          use x', (by simp [X']; tauto)
      . simp at hy ⊢
        obtain hy | hy := hy
        . obtain ⟨ x', ⟨ hx', hfx' ⟩ ⟩ := hy
          use x', (by simp [X'] at hx'; tauto)
        . use x, hx
          simp [hy]
    simp [this]
    use h_ins.1
    omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
  -- Induct on cardinality of X.
  obtain ⟨ n, hX ⟩ := hX
  revert X
  induction' n with i IH
  . intro X f hfi hX
    have : (image f X) = ∅
    . have hXe : X = ∅ := by exact has_card_zero.mp hX
      ext x
      simp [hXe]
    simp [this]
    have : X.card = 0 := by exact has_card_to_card hX
    simp [this]
  intro X f hfi hX
  -- IH: Assume holds for all X of size n, prove for set of size n+1.
  -- Consider X' = X \ {x}. We can create f' off of f.
  have hXc : X.card = i + 1 := by exact has_card_to_card hX
  have hXe : X ≠ ∅
  . intro contra
    have : X.card = 0 := by exact card_eq_zero_of_empty contra
    omega
  obtain ⟨ x, hx ⟩ := nonempty_def hXe
  set X' := X \ {x}
  have hX' : X'.has_card i
  . have := card_erase (by omega) hX ⟨ x, hx ⟩
    simp at this
    simp [X', this]
  have hX'c : X'.card = i := by exact has_card_to_card hX'
  set f':X' → Y := fun x ↦ f ⟨ x, by {
    have hx := x.2
    simp [X'] at hx
    tauto
  } ⟩
  have hf'i : Function.Injective f'
  . intro x1 x2 h
    simp [f'] at h
    specialize hfi h
    simp [coe_inj] at hfi
    exact hfi
  specialize IH hf'i hX'
  have hf' : (f ⟨x, hx⟩).val ∉ image f' X'
  . intro contra
    simp [f'] at contra
    obtain ⟨ x', hx', h ⟩ := contra
    simp [coe_inj] at h
    specialize hfi h
    simp [X'] at hx'
    contrapose! hx'; intro _
    simp at hfi
    exact hfi
  have hif : (image f' X').finite
  . have h : X'.finite := by use i
    exact (card_image h f').1
  have h_ins := card_insert hif hf'
  have : (image f X) = (image f' X' ∪ {↑(f ⟨x, hx⟩)})
  . ext y
    constructor <;> intro hy
    . simp at hy
      obtain ⟨ x', ⟨ hx', hfx' ⟩ ⟩ := hy
      simp
      by_cases hx'2 : x' = x
      . right
        simp [← hx'2, hfx']
      . left
        use x', (by simp [X']; tauto)
    . simp at hy ⊢
      obtain hy | hy := hy
      . obtain ⟨ x', ⟨ hx', hfx' ⟩ ⟩ := hy
        use x', (by simp [X'] at hx'; tauto)
      . use x, hx
        simp [hy]
  rw [this]
  omega

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  obtain ⟨ n, hx ⟩ := hX
  -- Induct on the cardinality of X, generalizing X.
  revert X
  induction' n with i IH
  . intro X hX
    have he : X = ∅ := by exact has_card_zero.mp hX
    simp [he]
    have he2 : (((∅:Set) ×ˢ Y):Set) = (∅:Set)
    . ext x
      simp
    simp [he2]
  -- IH: Assume holds for X' of size n, prove for X of size n+1.
  intro X hX
  have hXc : X.card = i + 1 := by exact has_card_to_card hX
  have hXe : X ≠ ∅
  . intro contra
    have : X.card = 0 := by exact card_eq_zero_of_empty contra
    omega
  obtain ⟨ x, hx ⟩ := nonempty_def hXe
  set X' := X \ {x}
  have hX' : X'.has_card i
  . have := card_erase (by omega) hX ⟨ x, hx ⟩
    simp at this
    simp [X', this]
  have hX'c : X'.card = i := by exact has_card_to_card hX'
  specialize IH hX'
  obtain ⟨ j, hY ⟩ := hY
  have hYc : Y.card = j := by exact has_card_to_card hY
  -- We'll need to union with {x} * Y and prove its cardinality is equal to Y.
  set xprod := ({x}:Set) ×ˢ Y
  have hxprod : xprod.has_card j
  . simp [xprod]
    -- Create the bijective mapping using y's.
    obtain ⟨ f, hf ⟩ := hY
    -- Use the slice so we don't run into double exists choose woes...
    have : (({x}:Set) ×ˢ Y) = SetTheory.Set.slice x Y
    . ext p
      simp
    rw [this]
    use fun p ↦ f ((mem_slice x p Y).mp p.2).choose
    constructor
    . intro p1 p2 h
      simp at h
      set c1 := (mem_slice x (↑p1) Y).mp p1.property
      set c2 := (mem_slice x (↑p2) Y).mp p2.property
      have hc1 := c1.choose_spec
      have hc2 := c2.choose_spec
      rw [← coe_inj, hc1, hc2]
      simp
      rw [← Fin.coe_inj] at h
      have := hf.1 h
      simp [this]
    . intro n
      have h_surj := hf.2 n
      obtain ⟨ y, hy ⟩ := h_surj
      set p := (⟨x, y⟩:OrderedPair)
      have hp : OrderedPair.toObject p ∈ slice x Y
      . rw [mem_slice]
        use y
      set p2 := (⟨ p, hp ⟩:(slice x Y))
      use p2
      simp
      set c := (mem_slice x (↑p2) Y).mp p2.property
      have hc := c.choose_spec
      unfold p2 at hc
      unfold p at hc
      have : c.choose = y
      . set d := c.choose -- For some reason required...
        simp [coe_inj] at hc
        simp [hc]
      simp [this, hy]
  have hxprodf : xprod.finite := by use j
  have hxprodc : xprod.card = j := by exact has_card_to_card hxprod
  have he : (X ×ˢ Y) = (X' ×ˢ Y) ∪ xprod
  . simp [xprod, SetTheory.Set.ext_iff]
    intro p
    constructor <;> intro h
    . obtain ⟨ x', hx', y, hy, hp ⟩ := h
      by_cases hx'2 : x' = x
      . right
        use y, hy
        simp [← hx'2, hp]
      . left
        simp [X']
        use x', (by tauto), y
    . obtain h | h := h
      . obtain ⟨ x', hx', y, hy, hp ⟩ := h
        simp [X'] at hx'
        use x', (by tauto), y, hy
      . obtain ⟨ y, hy, hp2 ⟩ := h
        use x, hx, y
  rw [he]
  constructor
  . exact (card_union IH.1 hxprodf).1
  have h_disj : Disjoint (X' ×ˢ Y) xprod
  . simp [disjoint_iff, SetTheory.Set.ext_iff]
    intro p x' hx' y hy hp contra
    simp [xprod] at contra
    obtain ⟨ y2, hy2, hp2 ⟩ := contra
    simp [hp2] at hp
    simp [X'] at hx'
    tauto
  have := card_union_disjoint IH.1 hxprodf h_disj
  simp [this, hxprodc, IH.2, hX'c, hYc, hXc]
  ring

abbrev f_to_power {A B : Set} : (B → A) → (A ^ B).toSubtype :=
  fun f ↦ ⟨ f, by {
    rw [SetTheory.Set.powerset_axiom]
    use f
  } ⟩

theorem f_to_power_surjective {A B : Set} : Function.Surjective (f_to_power (A:=A) (B:=B)) := by
  intro b
  have hb := b.2
  simp at hb
  obtain ⟨ f, hf ⟩ := hb
  use f
  simp [f_to_power, hf]

theorem f_to_power_injective {A B : Set} : Function.Injective (f_to_power (A:=A) (B:=B)) := by
  intro a1 a2 h
  simp [f_to_power] at h
  exact h

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := Function.surjInv f_to_power_surjective
  invFun := f_to_power
  left_inv := by {
    change Function.RightInverse (Function.surjInv _) f_to_power
    apply Function.rightInverse_surjInv
  }
  right_inv := by {
    change Function.LeftInverse (Function.surjInv _) f_to_power
    apply Function.leftInverse_surjInv
    constructor
    . exact f_to_power_injective
    . exact f_to_power_surjective
  }

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

open Classical in
/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  -- Induct on cardinality of X.
  obtain ⟨ i, hX ⟩ := hX
  obtain ⟨ j, hY ⟩ := hY
  have hYf : Y.finite := by use j
  revert X
  induction' i with i IH
  . intro X hX
    have he : X = ∅ := by exact has_card_zero.mp hX
    have hXc : X.card = 0 := by exact card_eq_zero_of_empty he
    simp [he]
    have goal : (((Y:Set) ^ (∅:Set)):Set).has_card 1
    . use fun _ ↦ Fin_mk 1 0 (by omega)
      constructor
      . intro f1 f2 _
        have hf1 := f1.2
        have hf2 := f2.2
        rw [powerset_axiom] at hf1 hf2
        obtain ⟨ f1', hf1' ⟩ := hf1
        obtain ⟨ f2', hf2' ⟩ := hf2
        simp [← coe_inj, ← hf1', ← hf2']
        ext x
        have hx := x.2
        simp at hx
      . intro n
        set f: (∅:Set) → Y := fun x ↦ ⟨ 1, by {
          have := x.2
          simp at this
        } ⟩
        use ⟨ f, by {
          rw [powerset_axiom]
          use f
        } ⟩
        have := mem_Fin' n
        obtain ⟨ x, hx, rfl ⟩ := this
        simp
        omega
    constructor
    . use 1
    . exact has_card_to_card goal
  -- Then IH holds for X \ {x} -> Y. Need to prove for X -> Y.
  intro X hX
  have hXc : X.card = i + 1 := by exact has_card_to_card hX
  have hXe : X ≠ ∅
  . intro contra
    have : X.card = 0 := by exact card_eq_zero_of_empty contra
    omega
  obtain ⟨ x, hx ⟩ := nonempty_def hXe
  set X' := X \ {x}
  have hX' : X'.has_card i
  . have := card_erase (by omega) hX ⟨ x, hx ⟩
    simp at this
    simp [X', this]
  have hX'c : X'.card = i := by exact has_card_to_card hX'
  have hYc : Y.card = j := by exact has_card_to_card hY
  specialize IH hX'
  -- We can do a product with Y and assert this cardinality is the desired result.
  have h_prod := card_prod IH.1 hYf
  -- Then assert equality of cardinality with (Y ^ X) by making a bijective function.
  have goal : (Y ^ X).has_card (Y.card ^ X.card)
  . have hProd : ((Y ^ X') ×ˢ Y).has_card (Y.card ^ X.card)
    . have := has_card_card h_prod.1
      rw [h_prod.2, IH.2, hX'c] at this
      rw [hXc]
      have : Y.card ^ i * Y.card = Y.card ^ (i + 1) := by ring
      rwa [← this]
    -- Easiest would be to create a bijective function from ((Y ^ X') ×ˢ Y) -> (Y ^ X).
    set g: ((Y ^ X') ×ˢ Y) → ((Y ^ X):Set) :=
      fun p ↦ ⟨ ((fun x ↦ if hx:(x.val ∈ X') then (((powerset_axiom (SetTheory.Set.fst p)).mp (by exact Subtype.property _)).choose ⟨ x, hx ⟩)
        else (SetTheory.Set.snd p)):X → Y),
      by {
        rw [powerset_axiom]
        use ((fun x ↦ if hx:(x.val ∈ X') then (((powerset_axiom (SetTheory.Set.fst p)).mp (by exact Subtype.property _)).choose ⟨ x, hx ⟩)
        else (SetTheory.Set.snd p)):X → Y)
      } ⟩
    have hg : Function.Bijective g
    . have x'_helper (x' : X') : x'.val ∈ X
      . have := x'.2
        simp [X'] at this
        tauto
      have x'_helper2 (x' : X) (hx' : x'.val ∉ X') : x' = ⟨ x, hx ⟩
      . simp [X', x'.2] at hx'
        simp [← hx']
      have hxX' : x ∉ X' := by simp [X']
      constructor
      . intro p1 p2 h
        simp [g, funext_iff] at h
        obtain ⟨ f1, y1, rfl ⟩ := mem_cartesian' p1
        obtain ⟨ f2, y2, rfl ⟩ := mem_cartesian' p2
        simp [mk_cartesian, coe_inj]
        constructor
        . have hf1 := f1.2
          have hf2 := f2.2
          rw [powerset_axiom] at hf1 hf2
          obtain ⟨ f1', hf1' ⟩ := hf1
          obtain ⟨ f2', hf2' ⟩ := hf2
          simp [← coe_inj, ← hf1', ← hf2']
          ext x'
          specialize h x' (x'_helper x')
          simp [x'.2] at h
          set c1 := (powerset_axiom ↑(fst (mk_cartesian f1 y1))).mp (fst (mk_cartesian f1 y1)).property
          set c2 := (powerset_axiom ↑(fst (mk_cartesian f2 y2))).mp (fst (mk_cartesian f2 y2)).property
          have hc1 := c1.choose_spec
          have hc2 := c2.choose_spec
          set d1 := c1.choose
          set d2 := c2.choose
          simp at hc1 hc2
          simp [← hf1'] at hc1
          simp [← hf2'] at hc2
          simp [← hc1, ← hc2, h]
        . specialize h x hx
          simp [hxX'] at h
          exact h
      . intro fXY
        have fXY2 := fXY.2
        rw [powerset_axiom] at fXY2
        obtain ⟨ fXY', h ⟩ := fXY2
        set y := fXY' ⟨ x, hx ⟩
        set f':X' → Y := fun x ↦ fXY' ⟨ x, x'_helper x ⟩
        have hf' : (f':Object) ∈ (Y ^ X')
        . rw [powerset_axiom]
          use f'
        use mk_cartesian ⟨ f', hf' ⟩ y
        simp [g]
        simp [← coe_inj, ← h]
        ext x'
        by_cases hx' : x'.val ∈ X' <;> simp [hx']
        . set c := (powerset_axiom ↑(fst (mk_cartesian ⟨↑f', hf'⟩ y))).mp (fst (mk_cartesian ⟨↑f', hf'⟩ y)).property
          have hc := c.choose_spec
          set d := c.choose
          simp at hc
          simp [hc, f']
        . have := x'_helper2 x' hx'
          simp [this, y]
    obtain ⟨ f, hf ⟩ := hProd
    have hg_inv := (Equiv.ofBijective g hg).symm.bijective
    have := Function.Bijective.comp hf hg_inv
    use f ∘ ⇑(Equiv.ofBijective g hg).symm
  constructor
  . use (Y.card ^ X.card)
  exact has_card_to_card goal

#check SetTheory.Set.prod_commutator

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  have h := (SetTheory.Set.prod_commutator A B)
  obtain ⟨ f, f_inv, hl, hr ⟩ := h
  use f
  constructor
  . exact Function.LeftInverse.injective hl
  . exact Function.RightInverse.surjective hr

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

#check SetTheory.Set.curry_equiv

/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by sorry

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by sorry

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by sorry

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by sorry

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  obtain ⟨ nA, hnA ⟩ := hA
  obtain ⟨ nB, hnB ⟩ := hB
  constructor <;> intro h
  . obtain ⟨ f, hf ⟩ := h
    -- Induct on the cardinality of A, generalizing everything else.
    revert A B nB
    induction' nA with i IH
    . intro A _ hA _ _ _ _
      have hA2 : A.card = 0 := by exact has_card_to_card hA
      simp [hA2]
    -- IH: If there is an injective f from any set A -> B, then |A| <= |B|.
    -- Now need to prove for A with one more element.
    intro A B hiA j hjB f hf
    -- Consider A - {a} mapped to B - {f(a)}. (A is empty can be handled trivially)
    by_cases hA : A = ∅
    . have hA2 : A.card = 0 := by exact card_eq_zero_of_empty hA
      simp [hA2]
    replace hA := nonempty_def hA
    obtain ⟨ a, hA ⟩ := hA
    set A' := A \ {a}
    set b := (f ⟨ a, hA ⟩)
    set B' := B \ ({b.val}:Set)
    -- Keeping f but without a is still injective and so IH holds.
    have hA'A : A' ⊆ A := by {
      unfold A'
      intro x hx
      simp at hx
      tauto
    }
    set f':A' → B' := fun a' ↦ ⟨ f ⟨ a', hA'A a'.1 a'.2 ⟩, by {
      unfold B'
      simp
      constructor
      . exact Subtype.property _
      -- Need to prove f' a' isn't = b. Can use injectivity.
      intro h
      unfold b at h
      rw [coe_inj] at h
      have := hf h
      simp at this
      have contra := a'.2
      unfold A' at contra
      simp [this] at contra
    } ⟩
    have hf' : Function.Injective f'
    . intro x1 x2 hf'
      unfold f' at hf'
      simp [coe_inj] at hf'
      have := hf hf'
      simp [coe_inj] at this
      exact this
    -- The <= relation still holds with both sides adding 1. (|B| = 0 can be handled trivially)
    have hB : B.card = j := by exact has_card_to_card hjB
    have hAc : A.card = i+1 := by exact has_card_to_card hiA
    match j with
    | 0 => {
      have hB2 : B = ∅ := by exact has_card_zero.mp hjB
      have hB := b.2
      simp [hB2] at hB
    }
    | j + 1 => {
      have hA' : A'.has_card i := by {
        have := card_erase (by norm_num) hiA ⟨ a, hA ⟩
        simp at this
        exact this
      }
      have hB' : B'.has_card j := by {
        have := card_erase (by norm_num) hjB b
        simp at this
        exact this
      }
      have hA'B'  := IH hA' j hB' f' hf'
      replace hA' : A'.card = i := by exact has_card_to_card hA'
      replace hB' : B'.card = j := by exact has_card_to_card hB'
      linarith
    }
  . -- We know there's a bijective f from A -> nA and g from nB -> B.
    -- Consider h = g(id(f)).
    have hnA2 := hnA
    have hnB2 := hnB
    rw [has_card_iff] at hnA hnB
    obtain ⟨ f, hf ⟩ := hnA
    obtain ⟨ g', hg' ⟩ := hnB
    have hB_inv : ∃ g:(Fin nB) → B, Function.Injective g
    . use Function.surjInv hg'.2
      apply Function.injective_surjInv
    obtain ⟨ g, hg ⟩ := hB_inv
    use fun a ↦ g ⟨ (f a), by {
      have := (f a).2
      rw [mem_Fin] at *
      obtain ⟨ x, hx1, hx2 ⟩ := this
      use x
      simp [hx2]
      have : nA ≤ nB
      . have : A.card = nA := by exact has_card_to_card hnA2
        have : B.card = nB := by exact has_card_to_card hnB2
        linarith
      linarith
    } ⟩
    intro a1 a2 ha
    simp at ha
    specialize hg ha
    simp at hg
    rw [coe_inj] at hg
    exact hf.1 hg

open Classical in
/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  -- Get a' from non-empty A.
  have ha' := nonempty_def hA
  obtain ⟨ a', ha' ⟩ := ha'
  -- For each b, if there is an a where f a = b, then use that.
  -- (Not axiom of choice since it's unique existence)
  -- Otherwise a'.
  set g:B → A := fun b ↦ if ha:(∃ a, f a = b) then ha.choose else ⟨ a', ha' ⟩
  use g
  intro a
  -- Surjectivity is easy since each a has a mapping through f a.
  use f a
  unfold g
  have h_exists : ∃ a_1, f a_1 = f a := by use a
  simp [h_exists]
  set c := of_eq_true (eq_true h_exists)
  have hc := c.choose_spec
  exact hf hc

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  -- Induction on cardinality of A, generalize everything else.
  obtain ⟨ n, hn ⟩ := hA
  obtain ⟨ m, hm ⟩ := hB
  have h1 : A.card = n := by exact has_card_to_card hn
  have h2 : B.card = m := by exact has_card_to_card hm
  rw [h1, h2]
  clear h1 h2
  revert A B m
  induction' n with i IH
  . intro A B hA m hB
    have hAe : A = ∅ := by exact has_card_zero.mp hA
    have hAB : (A ∪ B) = B
    . simp [hAe]
    have hAB2 : (A ∩ B) = ∅
    . simp [hAe, SetTheory.Set.ext_iff]
    simp [hAB, hAB2]
    exact (has_card_to_card hB).symm
  intro A B hAc j hBc
  -- IH step: consider A' = A - {a}.
  -- (If A is empty, this is trivial)
  by_cases hAe : A = ∅
  . have h1 : A.card = 0 := by exact card_eq_zero_of_empty hAe
    have h2 : A.card = i + 1 := by exact has_card_to_card hAc
    linarith
  have hAne := nonempty_def hAe
  obtain ⟨ a, ha ⟩ := hAne
  set A' := A \ ({a}:Set)
  have hAf : A.finite := by use (i+1)
  have hBf : B.finite := by use j
  have hA'As : A' ⊆ A
  . intro x
    simp [A']
    tauto
  have hA'f : A'.finite
  . exact (card_subset hAf hA'As).1
  -- IH, obtain equality of A'/B.
  have hA'c : A'.has_card i
  . have := card_erase (by norm_num) hAc ⟨ a, ha ⟩
    simp at this
    simp [A', this]
  specialize IH hA'c j hBc
  -- Then a is either in B or not.
  by_cases haB : a ∈ B
  . -- If so, then already in (A' or B).
    have hABe : A' ∪ B = A ∪ B
    . ext x
      simp [A']
      by_cases hxa : x = a
      . simp [hxa]
        tauto
      . simp [hxa]
    have hABp : (A' ∩ B).card + 1 = (A ∩ B).card
    . have hA'Bf : (A' ∩ B).finite
      . -- Can use subset result.
        have : (A' ∩ B) ⊆ A'
        . intro x
          simp
          tauto
        exact (card_subset hA'f this).1
      have haA'B : a ∉ (A' ∩ B)
      . simp [A']
      have h_ins := (card_insert hA'Bf haA'B).2
      have : (A' ∩ B ∪ {a}) = (A ∩ B)
      . ext x
        simp [A']
        by_cases hx : x = a <;> simp [hx]
        . tauto
      simp [← this, h_ins]
    rw [← hABe]
    linarith
  . -- Otherwise now in (A or B) whereas not previously.
    have hABe : A' ∩ B = A ∩ B
    . ext x
      simp [A']
      by_cases hxa : x = a
      . simp [hxa]
        tauto
      . simp [hxa]
    have hABp : (A' ∪ B).card + 1 = (A ∪ B).card
    . have hA'Bf : (A' ∪ B).finite
      . exact (card_union hA'f hBf).1
      have haA'B : a ∉ (A' ∪ B)
      . simp [A', haB]
      have h_ins := (card_insert hA'Bf haA'B).2
      have : (A' ∪ B ∪ {a}) = (A ∪ B)
      . ext x
        simp [A']
        by_cases hx : x = a <;> simp [hx]
        . tauto
      simp [← this, h_ins]
    rw [← hABe]
    linarith

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  -- Assume to the conary that all |A i| <= 1.
  by_contra h
  push_neg at h
  -- Then we need to show iUnion <= n.
  suffices goal : ((Fin n).iUnion A).card ≤ n
  . linarith
  clear hAcard
  -- Induct on n
  induction' n with i IH
  . have he : ((Fin 0).iUnion A) = ∅
    . ext x
      simp [mem_iUnion]
    simp [he]
  -- IH: iUnion <= n, need to show <= n+1 when adding another A i.
  set A':Fin i → Set := fun n ↦ A (SetTheory.Set.Fin.castSucc n)
  have hA' : ∀ i, (A' i).finite
  . intro i'
    specialize hA (SetTheory.Set.Fin.castSucc i')
    simp [A', hA]
  have h2 : (∀ (i : (Fin i)), (A' i).card < 2)
  . intro i'
    specialize h (SetTheory.Set.Fin.castSucc i')
    simp [A', h]
  specialize IH hA' h2
  -- card_union to get the required relation.
  have hA'f : ((Fin i).iUnion A').finite
  . -- Induction with repeated card_union.
    clear IH h2 hA h
    induction' i with i IH
    . have : ((Fin 0).iUnion A') = ∅
      . ext x
        simp [mem_iUnion]
      exact finite_of_empty this
    replace IH := IH (A := A') (by {
      intro i'
      specialize hA' (Fin.castSucc i')
      simp [hA']
    })
    specialize hA' (Fin_mk (i+1) i (by norm_num))
    have h_fin := (card_union IH hA').1
    have : (((Fin i).iUnion fun n ↦ A' (Fin.castSucc n)) ∪ A' (Fin_mk (i + 1) i (by norm_num))) = ((Fin (i + 1)).iUnion A')
    . ext x
      simp only [mem_union, mem_iUnion]
      constructor <;> intro h
      . obtain h | h := h
        . obtain ⟨ i', hi' ⟩ := h
          use Fin.castSucc i'
        . use (Fin_mk (i + 1) i (by norm_num))
      . obtain ⟨ i', hi' ⟩ := h
        by_cases hi'2 : i' < i
        . left
          use Fin_mk i i' hi'2
          simp [Fin_mk, Fin.castSucc, hi']
        . right
          replace hi'2 : i' = Fin_mk (i+1) i (by norm_num)
          . have hi'3 := i'.2
            rw [mem_Fin] at hi'3
            obtain ⟨ x, hx1, hx2 ⟩ := hi'3
            simp at hi'2
            simp at hx2
            simp
            linarith
          simp [← hi'2, hi']
    simp [← this, h_fin]
  have hAif : (A (Fin_mk (i+1) i (by norm_num))).finite
  . exact hA (Fin_mk (i+1) i (by norm_num))
  have h_union := (card_union hA'f hAif).2
  have : (Fin i).iUnion A' ∪ (A (Fin_mk (i + 1) i (by norm_num))) = ((Fin (i + 1)).iUnion A)
  . ext x
    simp only [mem_union, mem_iUnion]
    constructor <;> intro h
    . obtain h | h := h
      . obtain ⟨ i', hi' ⟩ := h
        use Fin.castSucc i'
      . use (Fin_mk (i + 1) i (by norm_num))
    . obtain ⟨ i', hi' ⟩ := h
      by_cases hi'2 : i' < i
      . left
        use Fin_mk i i' hi'2
        simp [Fin_mk, A', Fin.castSucc, hi']
      . right
        replace hi'2 : i' = Fin_mk (i+1) i (by norm_num)
        . have hi'3 := i'.2
          rw [mem_Fin] at hi'3
          obtain ⟨ x, hx1, hx2 ⟩ := hi'3
          simp at hi'2
          simp at hx2
          simp
          linarith
        simp [← hi'2, hi']
  rw [← this]
  specialize h (Fin_mk (i + 1) i (by norm_num))
  linarith

open Classical in
/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  have fin2_helper (n : Fin 2) : n = (Fin_mk 2 0 (by omega)) ∨ n = (Fin_mk 2 1 (by omega))
  . have h := mem_Fin' n
    obtain ⟨ x, hx, hx2 ⟩ := h
    rw [hx2]
    interval_cases x <;> tauto
  constructor <;> intro h
  . intro S hSX hSc
    have hS : S.has_card 2 := card_to_has_card (by omega) hSc
    -- Grab the two elements and then manually form the image bijection.
    obtain ⟨ f', ⟨ hfi, hfs ⟩ ⟩ := hS
    obtain ⟨ s1, hs1 ⟩ := hfs (Fin_mk 2 0 (by omega))
    obtain ⟨ s2, hs2 ⟩ := hfs (Fin_mk 2 1 (by omega))
    have hsne : s1 ≠ s2
    . intro contra
      simp [contra, hs2] at hs1
    -- To do this, need to prove image/S/Fin pair set equalities.
    have goal : (image f S).has_card 2
    . have hs1X : s1.val ∈ X := hSX s1 s1.2
      have hs2X : s2.val ∈ X := hSX s2 s2.2
      have hs1I : (f ⟨s1, hs1X⟩).val ∈ image f S
      . rw [mem_image]
        use ⟨ s1, hs1X ⟩, (by simp; exact Subtype.property _ )
      have hs2I : (f ⟨s2, hs2X⟩).val ∈ image f S
      . rw [mem_image]
        use ⟨ s2, hs2X ⟩, (by simp; exact Subtype.property _ )
      have image_helper (y : image f S) : y = ⟨ (f ⟨ s1, hs1X ⟩), hs1I ⟩ ∨ y = ⟨ (f ⟨ s2, hs2X ⟩), hs2I ⟩
      . have hy := y.2
        rw [mem_image] at hy
        obtain ⟨ s, hs, hfs ⟩ := hy
        have s_helper : s = ⟨ s1, hs1X ⟩ ∨ s = ⟨ s2, hs2X ⟩
        . -- Consider f' s. Can prove result using injectivity.
          obtain hfs | hfs := fin2_helper (f' ⟨ s, hs ⟩)
          . rw [← hs1] at hfs
            specialize hfi hfs
            simp [← hfi]
          . rw [← hs2] at hfs
            specialize hfi hfs
            simp [← hfi]
        obtain hs2 | hs2 := s_helper <;> simp [hs2] at hfs <;> simp [hfs]
      use fun y ↦ if y = ⟨ (f ⟨ s1, hs1X ⟩), hs1I ⟩ then (Fin_mk 2 0 (by omega)) else (Fin_mk 2 1 (by omega))
      constructor
      . intro y1 y2 h
        simp at h
        by_cases hy1 : y1 = ⟨ (f ⟨ s1, hs1X ⟩), hs1I ⟩ <;> simp [hy1] at h <;>
          by_cases hy2 : y2 = ⟨ (f ⟨ s1, hs1X ⟩), hs1I ⟩ <;> simp [hy2] at h
        . simp [hy1, hy2]
        . replace hy1 : y1 = ⟨ (f ⟨ s2, hs2X ⟩), hs2I ⟩
          . specialize image_helper y1
            tauto
          replace hy2 : y2 = ⟨ (f ⟨ s2, hs2X ⟩), hs2I ⟩
          . specialize image_helper y2
            tauto
          simp [hy1, hy2]
      . intro n
        by_cases hn : n = (Fin_mk 2 0 (by omega))
        . use ⟨ (f ⟨ s1, hs1X ⟩), hs1I ⟩
          simp [hn]
        . replace hn : n = (Fin_mk 2 1 (by omega))
          . specialize fin2_helper n
            tauto
          use ⟨ (f ⟨ s2, hs2X ⟩), hs2I ⟩
          have hne : ¬ (f ⟨ s2, hs2X ⟩) = (f ⟨ s1, hs1X ⟩)
          . intro contra
            specialize h contra
            simp [coe_inj] at h
            tauto
          simp [coe_inj, hne, hn]
    exact has_card_to_card goal
  . by_contra hf
    unfold Function.Injective at hf
    push_neg at hf
    obtain ⟨ x1, x2, hxf, hx ⟩ := hf
    -- Consider {x1, x2}.
    have hS : ({x1.val, x2.val}:Set) ⊆ X
    . intro x hx
      simp at hx
      obtain hx | hx := hx <;> simp [hx] <;> exact Subtype.property _
    have hx1 : x1.val ∈ ({x1.val, x2.val}:Set) := by simp
    have hx2 : x2.val ∈ ({x1.val, x2.val}:Set) := by simp
    have x_helper (x : ({x1.val, x2.val}:Set)) : x = ⟨ x1, hx1 ⟩ ∨ x = ⟨ x2, hx2 ⟩
    . have := x.2
      simp at this
      obtain h | h := this <;> simp [← h]
    have hSc : ({x1.val, x2.val}:Set).card = 2
    . have goal : ({x1.val, x2.val}:Set).has_card 2
      . use fun x ↦ if x = ⟨ x1, hx1 ⟩ then (Fin_mk 2 0 (by omega)) else (Fin_mk 2 1 (by omega))
        constructor
        . intro x1' x2'
          obtain hx1' | hx1' := x_helper x1' <;> obtain hx2' | hx2' := x_helper x2' <;> simp [hx1', hx2']
          . tauto
        . intro n
          by_cases hn : n = (Fin_mk 2 0 (by omega))
          . use ⟨ x1, hx1 ⟩
            simp [hn]
          . replace hn : n = (Fin_mk 2 1 (by omega))
            . specialize fin2_helper n
              tauto
            use ⟨ x2, hx2 ⟩
            simp [hn, coe_inj]
            tauto
      exact has_card_to_card goal
    specialize h ({x1.val, x2.val}:Set) hS hSc
    have contra : (image f {↑x1, ↑x2}).card = 1
    . have goal : (image f {↑x1, ↑x2}).has_card 1
      -- The image set is only made up of { f x1 }.
      have hfx1 : (f x1).val ∈ (image f {↑x1, ↑x2})
      . rw [mem_image]
        use x1, hx1
      . use fun x ↦ (Fin_mk 1 0 (by omega))
        constructor
        . intro y1 y2 _
          have image_helper (y : (image f {↑x1, ↑x2})) : y = ⟨ f x1, hfx1 ⟩
          . have hy := y.2
            rw [mem_image] at hy
            obtain ⟨ x, hx, hfx ⟩ := hy
            simp [coe_inj] at hx
            obtain hx | hx := hx <;> rw [hx] at hfx
            . simp [hfx]
            . rw [← hxf] at hfx
              simp [hfx]
          have hy1 : y1 = ⟨ f x1, hfx1 ⟩ := image_helper y1
          have hy2 : y2 = ⟨ f x1, hfx1 ⟩ := image_helper y2
          simp [hy1, hy2]
        . intro n
          have hn : n = (Fin_mk 1 0 (by omega))
          . have := mem_Fin' n
            obtain ⟨ x, hx, rfl ⟩ := this
            simp
            omega
          use ⟨ f x1, hfx1 ⟩
          simp [hn]
      exact has_card_to_card goal
    omega

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by sorry

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by sorry

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by sorry

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by sorry

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by sorry

/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by sorry

/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by sorry

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by sorry)
  else
    Fin_mk _ ((x:ℕ) - 1) (by sorry)

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by sorry) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by sorry)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by sorry

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by sorry

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
    have equiv : S i ≃ Permutations n := sorry
    use equiv, equiv.injective, equiv.surjective

  -- Hint: you might find `card_iUnion_card_disjoint` and `Permutations_finite` useful.
  sorry

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by sorry

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
