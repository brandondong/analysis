import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by {
      intro x
      rfl
    }
    symm := by {
      intro x y h
      simp [h]
    }
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  rw [Int.ofNat_eq, Int.natCast_eq, eq]
  rfl

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by {
    intro ⟨ a, b ⟩ ⟨ a', b' ⟩ h
    simp [Setoid.r] at *
    calc
      b + a' = a' + b := by ring
      _ = a + b' := h.symm
      _ = _ := by ring
  })

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by {
    intro x1 x2 x3
    obtain ⟨ a, b, h1 ⟩ := eq_diff x1
    obtain ⟨ c, d, h2 ⟩ := eq_diff x2
    obtain ⟨ e, f, h3 ⟩ := eq_diff x3
    rw [h1, h2, h3]
    simp only [add_eq, eq]
    ring
  }) (by {
    intro x
    obtain ⟨ a, b, h ⟩ := eq_diff x
    simp only [h, ofNat_eq, add_eq, eq]
    ring
  }) (by {
    intro x
    obtain ⟨ a, b, h ⟩ := eq_diff x
    simp only [h, neg_eq, add_eq, ofNat_eq, eq]
    ring
  })

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by {
    intro x1 x2
    obtain ⟨ a, b, rfl ⟩ := eq_diff x1
    obtain ⟨ c, d, rfl ⟩ := eq_diff x2
    simp only [add_eq, eq]
    ring
  }

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by {
    intro x1 x2
    obtain ⟨ a, b, rfl ⟩ := eq_diff x1
    obtain ⟨ c, d, rfl ⟩ := eq_diff x2
    simp only [mul_eq, eq]
    ring
  }
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by {
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring
  }
  mul_one := by {
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring
  }

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by {
    intro x1 x2 x3
    obtain ⟨ a, b, rfl ⟩ := eq_diff x1
    obtain ⟨ c, d, rfl ⟩ := eq_diff x2
    obtain ⟨ e, f, rfl ⟩ := eq_diff x3
    simp only [mul_eq, add_eq, eq]
    ring
  }
  right_distrib := by {
    intro x1 x2 x3
    obtain ⟨ a, b, rfl ⟩ := eq_diff x1
    obtain ⟨ c, d, rfl ⟩ := eq_diff x2
    obtain ⟨ e, f, rfl ⟩ := eq_diff x3
    simp only [mul_eq, add_eq, eq]
    ring
  }
  zero_mul := by {
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring
  }
  mul_zero := by {
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring
  }

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  simp only [natCast_eq, sub_eq, neg_eq, add_eq, eq]
  ring

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  -- Brute forcing by unwrapping definitions doesn't seem to work...
  -- Instead brute force by trying every positive/negative combination of a/b.
  have ha := trichotomous a
  obtain ha | ha := ha
  . left; exact ha
  have hb := trichotomous b
  obtain hb | hb := hb
  . right; exact hb
  obtain ha | ha := ha <;> obtain hb | hb := hb <;>
    obtain ⟨ x, hx, rfl ⟩ := ha <;> obtain ⟨ y, hy, rfl ⟩ := hb <;>
    simp only [natCast_eq, neg_eq, mul_eq, ofNat_eq, eq] at h <;>
    simp at h <;> obtain h | h := h <;> linarith

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have h2 : (a-b) * c = 0
  . calc
      (a - b) * c = a * c - b * c := by ring
      _ = b * c - b * c := by rw [h]
      _ = 0 := by ring
  have h3 := mul_eq_zero h2
  obtain h3 | h3 := h3
  . calc
      a = a - b + b := by ring
      _ = 0 + b := by rw [h3]
      _ = b := by ring
  . contradiction

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  rw [lt_iff]
  constructor <;> intro h
  . obtain ⟨ ⟨ t, ht ⟩, h ⟩ := h
    use t
    constructor
    . contrapose! h
      have h2 : (t:Int) = 0
      . simp [h]
      calc
        a = a + t - t := by ring
        _ = b - t := by rw [ht]
        _ = b - 0 := by rw [h2]
        _ = _ := by ring
    . exact ht
  . obtain ⟨ t, h1, h2 ⟩ := h
    constructor
    . use t
    . contrapose! h1
      have goal : (t:Int) = 0
      . calc
          (t:Int) = a + (t:Int) - a := by ring
          _ = b - a := by rw [h2]
          _ = b - b := by rw [h1]
          _ = _ := by ring
      simp only [natCast_eq, ofNat_eq, eq] at goal
      simp at goal
      exact goal

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨ x, hx1, hx2 ⟩ := h
  use x, hx1
  rw [hx2]
  ring

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨ x, hx1, hx2 ⟩ := hab
  obtain ⟨ c', hc'1, hc'2 ⟩ := hc
  use c' * x
  constructor
  . exact Nat.mul_ne_zero hc'1 hx1
  . simp at hc'2
    rw [hx2]
    have goal : c * x = ((c' * x:Nat):Int)
    . simp [hc'2]
    rw [← goal]
    ring

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨ x, hx1, hx2 ⟩ := h
  use x, hx1
  rw [hx2]
  ring

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  rw [le_iff] at *
  obtain ⟨ x, hx ⟩ := h
  use x
  rw [hx]
  ring

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨ x, hx1, hx2 ⟩ := hab
  obtain ⟨ y, hy1, hy2 ⟩ := hbc
  use (x+y)
  constructor
  . omega
  have h : (x:Int) + (y:Int) = (((x:ℕ) + (y:ℕ):ℕ):Int)
  . simp
  rw [hy2, hx2, ← h]
  ring

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  obtain h | h | h := trichotomous (a-b)
  . right; right
    calc
      a = a - b + b := by ring
      _ = 0 + b := by rw [h]
      _ = _ := by ring
  . left
    obtain ⟨ x, hx1, hx2 ⟩ := h
    rw [gt_iff_lt, lt_iff_exists_positive_difference]
    use x
    constructor
    . linarith
    calc
      a = a - b + b := by ring
      _ = x + b := by rw [hx2]
      _ = _ := by ring
  . right; left
    obtain ⟨ x, hx1, hx2 ⟩ := h
    rw [lt_iff_exists_positive_difference]
    use x
    constructor
    . linarith
    calc
      b = -(a - b - a) := by ring
      _ = -(-x - a) := by rw [hx2]
      _ = _ := by ring

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  intro ⟨ h1, h2 ⟩
  rw [gt_iff_lt] at h1
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨ x, hx1, hx2 ⟩ := h1
  obtain ⟨ y, hy1, hy2 ⟩ := h2
  rw [hx2] at hy2
  obtain ⟨ a, b, rfl ⟩ := eq_diff b
  simp only [natCast_eq, add_eq, eq] at hy2
  omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  rw [gt_iff_lt, lt_iff]
  tauto

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  rw [lt_iff]
  tauto

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        rw [le_iff_exists_add] at h
        obtain ⟨ x, hx ⟩ := h
        rw [le_iff]
        use x
        simp only [natCast_eq, add_eq, eq]
        omega
      | isFalse h =>
        apply isFalse
        contrapose! h
        rw [le_iff] at h
        rw [le_iff_exists_add]
        obtain ⟨ x, hx ⟩ := h
        simp only [natCast_eq, add_eq, eq] at hx
        use x
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor <;> intro h
  . specialize h 0
    simp at h
    simp [h]
  . intro a
    rw [h]
    ring

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by {
    intro a
    rw [le_iff]
    use 0
    ring
  }
  le_trans := by {
    intro a b c h1 h2
    rw [le_iff] at *
    obtain ⟨ x, hx ⟩ := h1
    obtain ⟨ y, hy ⟩ := h2
    use x+y
    have h : (x:Int) + (y:Int) = (((x:ℕ) + (y:ℕ):ℕ):Int)
    . simp
    rw [hy, hx, ← h]
    ring
  }
  lt_iff_le_not_ge := by {
    intro a b
    constructor <;> intro h
    . constructor
      . rw [le_iff]
        rw [lt_iff] at h
        obtain ⟨ ⟨ x, hx ⟩, _ ⟩ := h
        use x
      . intro h2
        rw [lt_iff_exists_positive_difference] at h
        rw [le_iff] at h2
        obtain ⟨ x, hx1, hx2 ⟩ := h
        obtain ⟨ y, hy ⟩ := h2
        rw [hx2] at hy
        obtain ⟨ a, b, rfl ⟩ := eq_diff a
        simp only [natCast_eq, add_eq, eq] at hy
        omega
    . obtain ⟨ h1, h ⟩ := h
      obtain ⟨ x, hx ⟩ := h1
      rw [lt_iff]
      constructor
      . use x
      contrapose! h
      rw [le_iff]
      use 0
      simp [h]
  }
  le_antisymm := by {
    intro a b h1 h2
    rw [le_iff] at *
    obtain ⟨ x, hx ⟩ := h1
    obtain ⟨ y, hy ⟩ := h2
    have goal : (y:Int) = 0
    . rw [hy] at hx
      obtain ⟨ a, b, rfl ⟩ := eq_diff b
      simp only [natCast_eq, add_eq, eq] at hx
      simp at hx
      have : y = 0 := by omega
      simp [this]
    simp [goal] at hy
    exact hy
  }
  le_total := by {
    intro a b
    obtain h | h | h := Int.trichotomous' a b
    . right
      rw [gt_iff_lt, lt_iff] at h
      obtain ⟨ x, hx ⟩ := h.1
      rw [le_iff]
      use x
    . left
      rw [lt_iff] at h
      obtain ⟨ x, hx ⟩ := h.1
      rw [le_iff]
      use x
    . left
      rw [le_iff]
      use 0
      simp [h]
  }
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  obtain ⟨ a, b, rfl ⟩ := eq_diff a
  simp only [ofNat_eq, neg_eq, mul_eq, eq]
  ring

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use fun n ↦ n ≥ 0
  simp
  constructor
  . intro n h
    rw [le_iff] at *
    obtain ⟨ x, hx ⟩ := h
    use x+1
    simp [hx]
  . use -1
    rw [lt_iff_exists_positive_difference]
    use 1
    constructor
    . linarith
    simp

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by sorry

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by sorry

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by sorry

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    sorry)
  invFun := sorry
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

end Section_4_1
