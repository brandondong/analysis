import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases h : x = 0
  . left
    exact h
  right
  -- If x is not zero, then we know there exists c < |a n|...
  obtain ⟨ a, ha, hab, rfl ⟩ := Real.boundedAwayZero_of_nonzero h; clear h
  rw [bounded_away_zero_def] at hab
  obtain ⟨ c, hc, hab ⟩ := hab
  -- We're going to have to construct a new a' which is equivalent to a.
  -- We know a is cauchy so we can consider e=c/2 and see the sign at a N.
  have hac := (Sequence.IsCauchy.coe a).mp ha
  specialize hac (c/2) (by linarith)
  obtain ⟨ N, hN ⟩ := hac
  unfold Section_4_3.dist at hN
  obtain h | h | h := lt_trichotomy (a N) 0
  . -- Nothing further in (a n) can change sign.
    right
    rw [Real.isNeg_def]
    use (fun n ↦ if n ≥ N then (a n) else (-c/2))
    have ha' : ((fun n ↦ if n ≥ N then (a n) else (-c/2)):Sequence).IsCauchy
    . rw [Sequence.IsCauchy.coe]
      intro e he
      rw [Sequence.IsCauchy.coe] at ha
      specialize ha e he
      obtain ⟨ M, ha ⟩ := ha
      use N+M
      intro j hj k hk
      have hj2 : j ≥ N := by omega
      have hk2 : k ≥ N := by omega
      simp [hj2, hk2]
      specialize ha j (by omega) k (by omega)
      exact ha
    split_ands
    . rw [boundedAwayNeg_def]
      use (c/2), (by linarith)
      intro n
      by_cases hn : n ≥ N <;> simp [hn]
      . specialize hN N (by omega) n hn
        specialize hab N
        rw [abs_of_neg h] at hab
        rw [abs_le] at hN
        linarith
      . linarith
    . exact ha'
    . rw [Real.LIM_eq_LIM ha ha', Sequence.equiv_iff]
      intro e he
      use N
      intro n hn
      simp [hn]
      linarith
  . specialize hab N
    simp [h] at hab
    linarith
  . left
    rw [Real.isPos_def]
    use (fun n ↦ if n ≥ N then (a n) else (c/2))
    have ha' : ((fun n ↦ if n ≥ N then (a n) else (c/2)):Sequence).IsCauchy
    . rw [Sequence.IsCauchy.coe]
      intro e he
      rw [Sequence.IsCauchy.coe] at ha
      specialize ha e he
      obtain ⟨ M, ha ⟩ := ha
      use N+M
      intro j hj k hk
      have hj2 : j ≥ N := by omega
      have hk2 : k ≥ N := by omega
      simp [hj2, hk2]
      specialize ha j (by omega) k (by omega)
      exact ha
    split_ands
    . rw [boundedAwayPos_def]
      use (c/2), (by linarith)
      intro n
      by_cases hn : n ≥ N <;> simp [hn]
      . specialize hN N (by omega) n hn
        specialize hab N
        rw [abs_of_pos h] at hab
        rw [abs_le] at hN
        linarith
    . exact ha'
    . rw [Real.LIM_eq_LIM ha ha', Sequence.equiv_iff]
      intro e he
      use N
      intro n hn
      simp [hn]
      linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  intro ⟨ h0, h ⟩
  rw [Real.isPos_def] at h
  obtain ⟨ a, ha, hac, rfl ⟩ := h
  rw [boundedAwayPos_def] at ha
  rw [← Real.LIM.zero, Real.LIM_eq_LIM hac (Sequence.IsCauchy.const _), Sequence.equiv_iff] at h0
  obtain ⟨ c, hc, ha ⟩ := ha
  contrapose! h0; clear h0
  use (c/2), (by linarith)
  intro N
  use N, (by omega)
  specialize ha N
  simp
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  intro ⟨ h0, h ⟩
  rw [Real.isNeg_def] at h
  obtain ⟨ a, ha, hac, rfl ⟩ := h
  rw [boundedAwayNeg_def] at ha
  rw [← Real.LIM.zero, Real.LIM_eq_LIM hac (Sequence.IsCauchy.const _), Sequence.equiv_iff] at h0
  obtain ⟨ c, hc, ha ⟩ := ha
  contrapose! h0; clear h0
  use (c/2), (by linarith)
  intro N
  use N, (by omega)
  specialize ha N
  simp
  rw [abs_of_neg (by linarith)]
  linarith

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rw [Real.isPos_def, Real.isNeg_def]
  intro ⟨ h1, h2 ⟩
  obtain ⟨ a, ha, hac, rfl ⟩ := h1
  obtain ⟨ b, hb, hbc, h ⟩ := h2
  rw [Real.LIM_eq_LIM hac hbc, Sequence.equiv_iff] at h
  rw [boundedAwayPos_def] at ha
  rw [boundedAwayNeg_def] at hb
  obtain ⟨ c, hc, ha ⟩ := ha
  obtain ⟨ d, hd, hb ⟩ := hb
  contrapose! h; clear h
  use c, hc
  intro N
  use N, (by omega)
  specialize ha N
  specialize hb N
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  rw [Real.isPos_def, Real.isNeg_def]
  constructor <;> intro h
  . obtain ⟨ a, hab, ha, rfl ⟩ := h
    use -a
    split_ands
    . rw [boundedAwayPos_def]
      rw [boundedAwayNeg_def] at hab
      obtain ⟨ c, hc, hac ⟩ := hab
      use c, hc
      intro n
      specialize hac n
      simp
      linarith
    . exact Sequence.IsCauchy.neg a ha
    . rw [Real.neg_LIM a ha]
  . obtain ⟨ a, hab, ha, hx ⟩ := h
    use -a
    have ha2 :=Sequence.IsCauchy.neg a ha
    split_ands
    . rw [boundedAwayNeg_def]
      rw [boundedAwayPos_def] at hab
      obtain ⟨ c, hc, hac ⟩ := hab
      use c, hc
      intro n
      specialize hac n
      simp
      linarith
    . exact ha2
    rw [Real.neg_def] at hx
    obtain ⟨ b, hb, rfl ⟩ := Real.eq_lim x
    rw [Real.ratCast_def, Real.LIM_mul (Sequence.IsCauchy.const _) hb] at hx
    rw [Real.LIM_eq_LIM hb ha2, Sequence.equiv_iff]
    rw [Real.LIM_eq_LIM (by {
      apply Sequence.IsCauchy.mul
      . exact (Sequence.IsCauchy.const _)
      . exact hb
    }) ha, Sequence.equiv_iff] at hx
    intro e he
    specialize hx e he
    obtain ⟨ N, hN ⟩ := hx
    use N
    intro n hn
    specialize hN n hn
    simp at hN
    simp
    have : -b n - a n = -(b n + a n) := by linarith
    rwa [this, abs_neg] at hN

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  rw [Real.isPos_def] at *
  obtain ⟨ x, hxb, hx, rfl ⟩ := hx
  obtain ⟨ y, hyb, hy, rfl ⟩ := hy
  use (x+y)
  split_ands
  . rw [boundedAwayPos_def] at *
    obtain ⟨ c, hc, hxc ⟩ := hxb
    obtain ⟨ d, hd, hyd ⟩ := hyb
    use c, hc
    intro n
    specialize hxc n
    specialize hyd n
    simp
    linarith
  . apply Sequence.IsCauchy.add
    . exact hx
    . exact hy
  . rw [Real.LIM_add hx hy]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  rw [Real.isPos_def] at *
  obtain ⟨ x, hxb, hx, rfl ⟩ := hx
  obtain ⟨ y, hyb, hy, rfl ⟩ := hy
  use x*y
  split_ands
  . rw [boundedAwayPos_def] at *
    obtain ⟨ c, hc, hxc ⟩ := hxb
    obtain ⟨ d, hd, hyd ⟩ := hyb
    use c*d, (by exact Left.mul_pos hc hd)
    intro n
    specialize hxc n
    specialize hyd n
    simp
    have hyn : (y n) ≥ 0 := by linarith
    calc
      _ ≤ c * (y n) := by exact (mul_le_mul_iff_of_pos_left hc).mpr hyd
      _ ≤ _ := by exact mul_le_mul_of_nonneg_right hxc hyn
  . apply Sequence.IsCauchy.mul
    . exact hx
    . exact hy
  . rw [Real.LIM_mul hx hy]

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor <;> intro h
  . rw [Real.isPos_def] at h
    obtain ⟨ a, hab, ha, hq ⟩ := h
    rw [ratCast_def, Real.LIM_eq_LIM (Sequence.IsCauchy.const _) ha, Sequence.equiv_iff] at hq
    rw [boundedAwayPos_def] at hab
    obtain ⟨ c, hc, hac ⟩ := hab
    -- q is arbitrarily close to (a n) and a is >= c.
    contrapose! hq
    use (c/2), (by linarith)
    intro N
    use N, (by omega)
    specialize hac N
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  . rw [Real.isPos_def]
    use fun _ ↦ q
    split_ands
    . rw [boundedAwayPos_def]
      use q, h
      simp
    . exact (Sequence.IsCauchy.const _)
    . simp [ratCast_def]

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  rw [Real.neg_iff_pos_of_neg]
  have : q < 0 ↔ (-q) > 0
  . simp
  rw [this]
  have := Real.pos_of_coe (-q)
  simp only [Rat.cast_neg] at this
  exact this

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  rw [gt_iff_lt, Real.lt_iff]
  simp
theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  rw [ge_iff_le, Real.le_iff, gt_iff_lt]
  tauto

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [Real.lt_iff]
  rw [Real.ratCast_sub, Real.neg_of_coe]
  simp

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  rw [Real.gt_iff]
  simp
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  rw [Real.lt_iff]
  simp

theorem zero_eq_helper (x y: Real) : x = y ↔ x - y = 0 := by
  constructor <;> intro h
  . simp [h]
  . contrapose! h
    exact sub_ne_zero_of_ne h

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  obtain h | h | h := Real.trichotomous (x-y)
  . right; right
    rwa [zero_eq_helper]
  . left
    rwa [Real.gt_iff]
  . right; left
    rwa [Real.lt_iff]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [Real.gt_iff, Real.lt_iff]
  exact not_pos_neg (x - y)

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rw [Real.gt_iff, zero_eq_helper]
  have := Real.not_zero_pos (x-y)
  contrapose! this
  tauto

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rw [← gt_iff_lt]
  have := Real.not_gt_and_eq y x
  tauto

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by
  rw [gt_iff_lt]

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [← gt_iff_lt, Real.gt_iff] at *
  have : z - x = (y-x) + (z-y) := by ring
  rw [this]
  exact pos_add hxy hyz

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [← gt_iff_lt, Real.gt_iff] at *
  ring_nf
  exact hxy

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [Real.le_iff] at *
  obtain h | h := hxy
  . left
    rw [mul_comm z x, mul_comm z y]
    exact mul_lt_mul_right h hz
  . right
    simp [h]

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  simp
  simp at hy
  have := Real.pos_mul hx hy
  suffices h : x * -y = -(x * y)
  . rwa [← h]
  ring

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by {
    intro a
    rw [Real.le_iff]
    tauto
  }
  le_trans := by {
    intro a b c hab hbc
    rw [Real.le_iff] at *
    obtain hab | rfl := hab
    . obtain hbc | rfl := hbc
      . left
        exact lt_trans hab hbc
      . tauto
    . exact hbc
  }
  lt_iff_le_not_ge := by {
    intro a b
    constructor <;> intro h
    . constructor
      . rw [le_iff]
        tauto
      . intro h2
        rw [le_iff] at h2
        obtain h2 | h2 := h2
        . have := Real.not_gt_and_lt a b
          tauto
        . have := Real.not_lt_and_eq a b
          tauto
    . obtain ⟨ h1, h2 ⟩ := h
      rw [Real.le_iff] at *
      tauto
  }
  le_antisymm := by {
    intro a b hab hba
    rw [le_iff] at *
    obtain hab | hab := hab
    . obtain hba | hba := hba
      . have := Real.not_gt_and_lt a b
        tauto
      exact hba.symm
    exact hab
  }
  le_total := by {
    intro a b
    simp only [le_iff]
    have := Real.trichotomous' a b
    tauto
  }
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) Linear Orders come with a definition of absolute value |.|
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  simp [_root_.abs, max, SemilatticeSup.sup, abs]
  obtain h | h | h := Real.trichotomous x <;> simp [h]
  . intro h2
    rw [Real.le_iff] at h2
    obtain h2 | h2 := h2
    . rw [Real.lt_iff] at h2
      contrapose! h2
      have : x - -x = x + x := by ring
      rw [this]
      have := Real.pos_add h h
      have h3 := Real.not_pos_neg (x+x)
      contrapose! h3
      use this
    exact h2.symm
  . have h2 : ¬ x.IsPos
    . have := Real.not_pos_neg x
      contrapose! this
      use this
    simp [h2]
    intro h3
    rw [Real.lt_iff] at h3
    contrapose! h3
    simp at h
    have := Real.pos_add h h
    have : -x - x = -x + -x := by ring
    rw [this]; clear this
    have h3 := Real.not_pos_neg (-x + -x)
    contrapose! h3
    use this

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [Real.div_eq]
  have hy2 := Real.inv_of_pos hy
  exact Real.pos_mul hx hy2

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

theorem add_le_add_left : ∀ (a b : Real), a ≤ b → ∀ (c : Real), c + a ≤ c + b := by
  intro a b h c
  rw [Real.le_iff] at *
  obtain h | h := h
  . have := Real.add_lt_add_right c h
    left
    rwa [add_comm c a, add_comm c b]
  . simp [h]

theorem mul_lt_mul_of_pos_left : ∀ (a b c : Real), a < b → 0 < c → c * a < c * b := by
  intro a b c h hc
  have : c.IsPos := by exact (Real.isPos_iff c).mpr hc
  have := Real.mul_lt_mul_right h this
  rwa [mul_comm c a, mul_comm c b]

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by {
    intro a b h c
    exact add_le_add_left a b h c
  }
  add_le_add_right := by {
    intro a b h c
    have := add_le_add_left a b h c
    rwa [add_comm a c, add_comm b c]
  }
  mul_lt_mul_of_pos_left := by {
    intro a b c h hc
    exact mul_lt_mul_of_pos_left a b c h hc
  }
  mul_lt_mul_of_pos_right := by {
    intro a b c h hc
    have := mul_lt_mul_of_pos_left a b c h hc
    rwa [mul_comm a c, mul_comm b c]
  }
  le_of_add_le_add_left := by {
    intro a b c h
    contrapose! h
    have := Real.add_lt_add_right a h
    rwa [add_comm a c, add_comm a b]
  }
  zero_le_one := by {
    rw [le_iff, lt_iff]
    left
    simp [Real.isPos_def]
    use fun _ ↦ 1
    split_ands
    . rw [boundedAwayPos_def]
      use 1, (by linarith)
      simp
    . exact Sequence.IsCauchy.const _
    . exact LIM.one.symm
  }

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  sorry

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  -- We can find a rational lower bound of (y-x)/2.
  -- Then, using cauchy property, convert x/y into sequences and find rational value where
  -- it changes less than lower bound.
  sorry

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  apply existsUnique_of_exists_of_unique
  . -- Consider a N where all subsequent are 1/2 bounded away.
    obtain ⟨ a, ha, rfl ⟩ := Real.eq_lim x
    have ha := ha
    rw [Sequence.IsCauchy.coe] at ha
    specialize ha (1/2) (by linarith)
    obtain ⟨ N, hN ⟩ := ha
    unfold Section_4_3.dist at hN
    obtain ⟨ fl, hfl ⟩ := exists_floor (a N)
    -- Then the true value of a is within that bound.
    -- The possibilities of the integer floor are therefore the floor of a N, a N - 1, or a N + 1.
    -- If x < floor(a N), then we know it's floor(a N) - 1.
    obtain h | h := lt_or_ge (LIM a) fl
    . use (fl-1)
      constructor
      . rw [le_iff, lt_iff, Real.neg_iff_pos_of_neg]
        left
        simp
        have : (LIM a - (↑fl - 1)) = (LIM a + 1 - ↑fl) := by ring
        rw [this]; clear this
        rw [isPos_def]
        sorry
      . simp [h]
    -- Otherwise if x >= floor(a N) + 1, then it's floor(a N) + 1.
    obtain h2 | h2 := Or.symm (lt_or_ge (LIM a) (fl + 1))
    . use (fl+1)
      constructor
      . simp [h2]
      . simp
        rw [lt_iff, Real.neg_iff_pos_of_neg]
        have : (-(LIM a - (↑fl + 1 + 1))) = ((↑fl + 2) - LIM a) := by ring
        rw [this]; clear this
        rw [isPos_def]
        sorry
    -- Otherwise use floor(a N).
    use fl
  intro n1 n2 ⟨ hn1l, hn1r ⟩ ⟨ hn2l, hn2r ⟩
  -- Prove by contradiction.
  by_contra h
  -- wlog, consider n1 < n2.
  wlog hn : n1 < n2
  . exact this x n2 n1 hn2l hn2r hn1l hn1r (by omega) (by omega)
  clear h
  have hn2 : n1+1 ≤ n2 := by omega
  have hn3 : n1+1 ≤ (n2:Real)
  . norm_cast
  linarith

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by sorry

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by sorry

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by sorry

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by sorry

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by sorry

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by sorry

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by sorry

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by sorry

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by sorry

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  sorry
/- Additional exercise: What happens if z is negative? -/

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by sorry

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by sorry

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  sorry

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by sorry

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by sorry

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by sorry

end Chapter5
