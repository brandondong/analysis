import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of ℕ and ℤ.

- Equivalence with the Mathlib rationals `_root_.Rat` (or `ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers `ℕ` and integers `ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by {
      intro x
      simp
    }
    symm := by {
      intro x y h
      simp [h]
    }
    trans := by {
      intro⟨ a,b,_ ⟩ ⟨ c,d,hd ⟩ ⟨ e,f,_ ⟩ h1 h2; simp_all
      -- Multiply both equations and cancel.
      have h3 := congrArg₂ (· * ·) h1 h2; simp at h3
      have h4 : (c * d) * (a * f) = (c * d) * (e * b) := by linarith
      -- d is not zero but c might be...
      by_cases hc : c = 0
      . have ha : a = 0
        . simp [hc] at h1
          tauto
        have he : e = 0
        . simp [hc] at h2
          tauto
        simp [ha, he]
      have hcd : c * d ≠ 0
      . contrapose! hd
        rw [mul_eq_zero] at hd
        tauto
      exact mul_left_cancel₀ hcd h4
    }
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd, Setoid.r]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Decidability of equality. Hint: modify the proof of `DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the `Quotient` API.
-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m)
  . intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- We're trying to prove equality of Quotient.mk ⟨ a,b,h ⟩ = ... is decidable.
    -- Quotient.mk ⟨ a,b,h ⟩ is just a // b???
    set q1 := Quotient.mk PreRat.instSetoid ⟨ a,b,hb ⟩
    set q2 := Quotient.mk PreRat.instSetoid ⟨ c,d,hd ⟩
    have h1 : q1 = a // b
    . unfold Rat.formalDiv
      simp [hb, q1]
    have h2 : q2 = c // d
    . unfold Rat.formalDiv
      simp [hd, q2]
    rw [h1, h2, Rat.eq a c hb hd]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    calc
      _ = (a*b')*d*d' + b*b'*(c*d') := by ring
      _ = (a'*b)*d*d' + b*b'*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by {
    intro ⟨ a1, b1, hb1 ⟩ ⟨ c1, d1, hd1 ⟩ ⟨ a2, b2, hb2 ⟩ ⟨ c2, d2, hd2 ⟩ h1 h2
    simp_all [Setoid.r]
    have h3 := congrArg₂ (· * ·) h1 h2; simp at h3
    linarith
  })

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by {
    intro ⟨ a, b, hb ⟩ ⟨ c, d, hd ⟩
    simp_all [Setoid.r]
  })

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  simp [coe_Nat_eq, of_Nat_eq, add_eq]

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  simp [coe_Int_eq, add_eq]

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  simp [coe_Int_eq, mul_eq]

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro x1 x2 h
  simp only [coe_Int_eq] at h
  have : (1:ℤ) ≠ 0 := by norm_num
  have := Rat.eq x1 x2 this this
  simp [h] at this
  exact this

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro ⟨ a, b, hb ⟩ ⟨ c, d, hd ⟩ h
    simp_all [Setoid.r]
    -- hint: split into the `a=0` and `a≠0` cases
    by_cases ha : a = 0 <;> simp [ha]
    . have hc : c = 0
      . simp [ha] at h
        tauto
      simp [hc]
    . have hc : ¬ c = 0
      . contrapose! ha
        simp [ha] at h
        tauto
      simp [hc]
      linarith
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
) (by {
  intro a
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff a
  have : (1:ℤ) ≠ 0 := by omega
  simp [of_Nat_eq, add_eq 0 a this hb]
}) (by {
  intro a
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff a
  simp [neg_eq a hb, add_eq (-a) a hb hb]
  simp only [of_Nat_eq]
  have h1 : (1:ℤ) ≠ 0 := by omega
  have : b * b ≠ 0
  . contrapose! hb
    simp at hb
    tauto
  simp [eq _ _ this h1]
  ring
})

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by {
    intro x y
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    simp only [add_eq _ _ hb hd, add_eq _ _ hd hb]
    have h1 : b * d ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    have h2 : d * b ≠ 0
    . contrapose! h1
      linarith
    simp [eq _ _ h1 h2]
    ring
  }

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by {
    intro x y
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    simp only [mul_eq _ _ hb hd, mul_eq _ _ hd hb]
    have h1 : b * d ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    have h2 : d * b ≠ 0
    . contrapose! h1
      linarith
    simp [eq _ _ h1 h2]
    ring
  }
  mul_assoc := by {
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    simp only [mul_eq _ _ hb hd]
    have hbd : b * d ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    simp only [mul_eq _ _ hbd hf, mul_eq _ _ hd hf]
    have hdf : d * f ≠ 0
    . contrapose! hd
      simp at hd
      tauto
    simp only [mul_eq _ _ hb hdf]
    have hbdf : b * d * f ≠ 0
    . contrapose! hdf
      simp at hdf
      tauto
    have hbdf2 : b * (d * f) ≠ 0
    . contrapose! hbdf
      linarith
    simp [eq _ _ hbdf hbdf2]
    ring
  }
  one_mul := by {
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    simp [of_Nat_eq]
    have : (1:ℤ) ≠ 0 := by omega
    simp [mul_eq _ _ this hb]
  }
  mul_one := by {
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    simp [of_Nat_eq]
    have : (1:ℤ) ≠ 0 := by omega
    simp [mul_eq _ _ hb this]
  }

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by {
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [add_eq _ _ hd hf, mul_eq _ _ hb hd, mul_eq _ _ hb hf]
    have hdf : d * f ≠ 0
    . contrapose! hf
      simp at hf
      tauto
    have hbd : b * d ≠ 0
    . contrapose! hd
      simp at hd
      tauto
    have hbf : b * f ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    rw [mul_eq _ _ hb hdf, add_eq _ _ hbd hbf]
    have hbdf : (b * (d * f)) ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    have hbdbf : (b * d * (b * f)) ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    rw [eq _ _ hbdf hbdbf]
    ring
  }
  right_distrib := by {
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [add_eq _ _ hb hd, mul_eq _ _ hb hf, mul_eq _ _ hd hf]
    have hbd : b * d ≠ 0
    . contrapose! hd
      simp at hd
      tauto
    have hbf : b * f ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    have hdf : d * f ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    rw [mul_eq _ _ hbd hf, add_eq _ _ hbf hdf]
    have hbdf : (b * d * f) ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    have h : (b * f * (d * f)) ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    rw [eq _ _ hbdf h]
    ring
  }
  zero_mul := by {
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    simp [of_Nat_eq]
    have : (1:ℤ) ≠ 0 := by omega
    rw [mul_eq _ _ this hb]
    have h : 1 * b ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    rw [eq _ _ h this]
    ring
  }
  mul_zero := by {
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    simp [of_Nat_eq]
    have : (1:ℤ) ≠ 0 := by omega
    rw [mul_eq _ _ hb this]
    have h : b * 1 ≠ 0
    . contrapose! hb
      simp at hb
      tauto
    rw [eq _ _ h this]
    ring
  }
  mul_assoc := by {
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [mul_eq _ _ hb hd, mul_eq _ _ hd hf]
    have hbd : b * d ≠ 0
    . contrapose! hd
      simp at hd
      tauto
    have hdf : d * f ≠ 0
    . contrapose! hd
      simp at hd
      tauto
    rw [mul_eq _ _ hbd hf, mul_eq _ _ hb hdf]
    have h1 : (b * d * f) ≠ 0
    . contrapose! hd
      simp at hd
      tauto
    have h2 : (b * (d * f)) ≠ 0
    . contrapose! hd
      simp at hd
      tauto
    rw [eq _ _ h1 h2]
    ring
  }
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro ⟨ a, b, hb, h1 ⟩ ⟨ c, d, hd, h2 ⟩ h
  simp at h
  change a // b = c // d at h
  have hb2 : (b:ℤ) ≠ 0 := by omega
  have hd2 : (d:ℤ) ≠ 0 := by omega
  rw [eq _ _ hb2 hd2] at h
  simp [Rat.eq_iff_mul_eq_mul, h]

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by {
    use 1 // 1, 0 // 1
    intro contra
    have h : (1:ℤ) ≠ 0 := by omega
    rw [eq _ _ h h] at contra
    simp at contra
  }
  mul_inv_cancel := by {
    intro a h
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff a
    simp [of_Nat_eq]
    rw [of_Nat_eq] at h
    have h1 : (1:ℤ) ≠ 0 := by omega
    change ¬ a // b = ↑0 // 1 at h
    simp [eq _ _ hb h1] at h
    rw [inv_eq _ hb, mul_eq _ _ hb h]
    have hba : (b *a) ≠ 0
    . contrapose! h
      simp at h
      tauto
    rw [eq _ _ hba h1]
    ring
  }
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by
  rw [Rat.div_eq]
  have h6 : (6:ℤ) ≠ 0 := by omega
  rw [Rat.inv_eq _ h6]
  have h4 : (4:ℤ) ≠ 0 := by omega
  have h5 : (5:ℤ) ≠ 0 := by omega
  rw [Rat.mul_eq _ _ h4 h5]
  have h45 : (4 * 5:ℤ) ≠ 0 := by omega
  have h10 : (10:ℤ) ≠ 0 := by omega
  rw [Rat.eq _ _ h45 h10]
  ring

/-- Definition of subtraction -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by {
    intro x y
    simp
  }
  map_mul' := by {
    intro x y
    simp
  }

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  have h1 : (1:ℤ) ≠ 0 := by omega
  have ha := Int.lt_trichotomy a 0
  by_cases ha2 : a = 0
  . left
    simp only [ha2, of_Nat_eq]
    simp [eq _ _ hb h1]
  replace ha : a < 0 ∨ 0 < a := by tauto
  clear ha2
  have hb2 := Int.lt_trichotomy b 0
  replace hb2 : b < 0 ∨ 0 < b := by tauto
  obtain ha | ha := ha <;> obtain hb2 | hb2 := hb2
  . right; left
    use -a, -b
    use (by omega), (by omega)
    simp
    rw [div_eq, coe_Int_eq, coe_Int_eq, inv_eq _ h1, mul_eq _ _ h1 hb, eq _ _ hb (by omega)]
    ring
  . right; right
    use -a//b
    constructor
    . use -a, b
      use (by omega), (by omega)
      rw [div_eq, coe_Int_eq, coe_Int_eq, inv_eq _ h1, mul_eq _ _ h1 hb, neg_eq _ hb, eq _ _ hb (by omega)]
      ring
    . simp
  . right; right
    use -a//b
    constructor
    . use a, -b
      use (by omega), (by omega)
      rw [div_eq, neg_eq _ hb, coe_Int_eq, coe_Int_eq, inv_eq _ h1, mul_eq _ _ h1 (by omega), eq _ _ hb (by omega)]
      ring
    . simp
  . right; left
    use a, b
    use (by omega), (by omega)
    rw [div_eq, coe_Int_eq, coe_Int_eq, inv_eq _ h1, mul_eq _ _ h1 hb, eq _ _ hb (by omega)]
    ring

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  intro ⟨ h1, h2 ⟩
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ x, y, hx, hy, h3 ⟩ := h2
  rw [of_Nat_eq, eq _ _ (by omega) (by omega)] at h1
  simp at h1
  rw [h1, div_eq, coe_Int_eq, coe_Int_eq, inv_eq _ (by omega), mul_eq _ _ (by omega) (by omega), eq _ _ hb (by omega)] at h3
  simp at h3
  omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  intro ⟨ h1, h2 ⟩
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  rw [of_Nat_eq, eq _ _ (by omega) (by omega)] at h1
  simp at h1
  obtain ⟨ c, h3, h4 ⟩ := h2
  obtain ⟨ x, y, hx, hy, h3 ⟩ := h3
  rw [h1, h3, div_eq, coe_Int_eq, coe_Int_eq, inv_eq _ (by omega), mul_eq _ _ (by omega) (by omega), neg_eq _ (by omega), eq _ _ (by omega) (by omega)] at h4
  simp at h4
  omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  intro ⟨ h1, h2 ⟩
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ x, h2, h3 ⟩ := h2
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff x
  obtain ⟨ x1, y1, hx1, hy1, h4 ⟩ := h1
  obtain ⟨ x2, y2, hx2, hy2, h5 ⟩ := h2
  rw [h4, h5, div_eq, div_eq] at h3
  simp only [coe_Int_eq] at h3
  rw [inv_eq _ (by omega), inv_eq _ (by omega), mul_eq _ _ (by omega) (by omega), mul_eq _ _ (by omega) (by omega), neg_eq _ (by omega), eq _ _ (by omega) (by omega)] at h3
  simp at h3
  have : x1 * y2 > 0 := by exact Int.mul_pos hx1 hy2
  have : x2 * y1 > 0 := by exact Int.mul_pos hx2 hy1
  omega

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  rw [gt_iff_lt, lt_iff, isNeg]
  constructor <;> intro h
  . obtain ⟨ r, hr, hr2 ⟩ := h
    obtain ⟨ a, b, ha, hb, hr3 ⟩ := hr
    use a, b, ha, hb
    have : x - y = r
    . calc
        x - y = -(y - x) := by ring
        _ = -(-r) := by rw [hr2]
        _ = _ := by ring
    rw [this, hr3]
  . use (x-y), h
    ring
theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  rw [gt_iff_lt, ge_iff_le, le_iff]
  tauto

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  obtain h | h | h := trichotomous (x-y)
  . right; right
    calc
      x = x - y + y := by ring
      _ = 0 + y := by rw [h]
      _ = _ := by ring
  . left
    simp [gt_iff, h]
  . right; left
    simp [lt_iff, h]

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by
  intro h
  rw [gt_iff, lt_iff] at h
  simp [not_pos_and_neg] at h

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  intro h
  rw [gt_iff] at h
  have := not_zero_and_pos (x-y)
  have : x - y = 0
  . calc
      x - y = y - y := by rw [h.2]
      _ = 0 := by ring
  tauto

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  intro h
  rw [lt_iff] at h
  have := not_zero_and_neg (x-y)
  have : x - y = 0
  . calc
      x - y = y - y := by rw [h.2]
      _ = 0 := by ring
  tauto

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by
  rw [gt_iff_lt]

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  obtain ⟨ a, ha1, ha2 ⟩ := hxy
  obtain ⟨ b, hb1, hb2 ⟩ := hyz
  use (a+b)
  constructor
  . obtain ⟨ x1, y1, hx1, hy1, rfl ⟩ := ha1
    obtain ⟨ x2, y2, hx2, hy2, rfl ⟩ := hb1
    have hy1y2 : y1 * y2 > 0 := by exact Int.mul_pos hy1 hy2
    have hx1y2 : x1 * y2 > 0 := by exact Int.mul_pos hx1 hy2
    have hy1x2 : y1 * x2 > 0 := by exact Int.mul_pos hy1 hx2
    have h2 : 1 * y1 * (1 * y2) = y1 * y2 := by ring
    use x1*y2 + y1*x2, y1*y2, (by omega), hy1y2
    have h1 : (1:ℤ) ≠ 0 := by omega
    simp only [div_eq, coe_Int_eq]
    simp only [inv_eq _ h1]
    rw [mul_eq _ _ h1 (by omega), mul_eq _ _ h1 (by omega), mul_eq _ _ h1 (by omega), add_eq _ _ (by omega) (by omega)]
    rw [eq _ _ (by omega) (by omega)]
    ring
  . calc
      x - z = x - y + (y - z) := by ring
      _ = -a + (y - z) := by rw [ha2]
      _ = -a + -b := by rw [hb2]
      _ = _  := by ring

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  obtain ⟨ r, hr, hr2 ⟩ := hxy
  use r, hr
  have : x + z - (y + z) = x - y := by ring
  simp [this, hr2]

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  obtain ⟨ r, hr, hr2 ⟩ := hxy
  use r*z
  constructor
  . obtain ⟨ x1, y1, hx1, hy1, rfl ⟩ := hz
    obtain ⟨ x2, y2, hx2, hy2, rfl ⟩ := hr
    have h1 : (1:ℤ) ≠ 0 := by omega
    simp only [div_eq, coe_Int_eq, inv_eq _ h1]
    rw [mul_eq _ _ h1 (by omega), mul_eq _ _ h1 (by omega), mul_eq _ _ (by omega) (by omega)]
    have hx2x1 : x2 * x1 > 0 := by exact Int.mul_pos hx2 hx1
    have hy2y1 : y2 * y1 > 0 := by exact Int.mul_pos hy2 hy1
    have he : 1 * y2 * (1 * y1) = y2 * y1 := by ring
    use x2*x1, y2*y1, hx2x1, hy2y1
    simp only [div_eq, coe_Int_eq]
    rw [inv_eq _ h1, mul_eq _ _ h1 (by omega), eq _ _ (by omega) (by omega)]
    ring
  . calc
      x * z - y * z = (x - y) * z := by ring
      _ = -r * z := by rw [hr2]
      _ = _ := by ring

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by sorry
  add_le_add_right := by sorry
  mul_lt_mul_of_pos_left := by sorry
  mul_lt_mul_of_pos_right := by sorry
  le_of_add_le_add_left := by sorry
  zero_le_one := by sorry

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  sorry


/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    sorry)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by sorry
  map_mul' := by sorry

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
