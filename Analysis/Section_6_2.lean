import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals {name}`EReal`, particularly with regard to the supremum
  operation {name}`sSup` and infimum operation {name}`sInf`.

-/

open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp <;> tauto

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by rw [lt_iff]; exact ⟨le_top, real_neq_infty 3⟩


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := bot_lt_top


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := by
  rw [EReal.le_iff]
  obtain ⟨ y, rfl ⟩ | h := EReal.def x
  . left
    use y, y
  . simp [h]

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := by
  have hx := EReal.def x
  have hy := EReal.def y
  obtain ⟨ x, rfl ⟩ | rfl | rfl := hx
  . obtain ⟨ y, rfl ⟩ | rfl | rfl := hy
    . norm_cast
      exact lt_trichotomy x y
    . simp
    . simp
  . obtain ⟨ y, rfl ⟩ | rfl | rfl := hy
    . simp
    . simp
    . right; right
      exact bot_lt_top
  . obtain ⟨ y, rfl ⟩ | rfl | rfl := hy
    . simp
    . left
      exact bot_lt_top
    . simp

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by
  intro h
  rw [EReal.lt_iff] at h
  tauto

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by
  intro h
  rw [gt_iff_lt, EReal.lt_iff] at h
  tauto

theorem EReal.not_ge_top (x:ℝ) : ¬ ((⊤:EReal) ≤ x) := by
  intro h
  rw [le_iff] at h
  obtain h | h | h := h
  . obtain ⟨ y, z, h, _ ⟩ := h
    have := EReal.real_neq_infty y
    tauto
  . have := EReal.real_neq_infty x
    tauto
  . tauto

theorem EReal.not_le_bottom (x:ℝ) : ¬ (x ≤ (⊥:EReal)) := by
  intro h
  rw [le_iff] at h
  obtain h | h | h := h
  . obtain ⟨ y, z, h, _ ⟩ := h
    have := EReal.real_neq_infty z
    tauto
  . tauto
  . tauto

theorem EReal.le_top (x:EReal) : x ≤ ⊤ := by
  obtain ⟨ x, rfl ⟩ | rfl | rfl := EReal.def x
  . simp [le_iff]
  . simp
  . simp

theorem EReal.bottom_le (x:EReal) : ⊥ ≤ x := by
  obtain ⟨ x, rfl ⟩ | rfl | rfl := EReal.def x
  . simp only [le_iff]
    tauto
  . simp
  . simp

theorem EReal.top_le_eq_top {x:EReal} (h: ⊤ ≤ x) : x = ⊤ := by
  simp [le_iff] at h
  tauto

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := by
  intro h
  rw [gt_iff_lt, EReal.lt_iff, EReal.lt_iff] at h
  obtain ⟨ ⟨ h1, h3 ⟩, h2, h4 ⟩ := h; clear h4
  have hx := EReal.def x
  have hy := EReal.def y
  obtain ⟨ x, rfl ⟩ | rfl | rfl := hx
  . obtain ⟨ y, rfl ⟩ | rfl | rfl := hy
    . simp at h1 h2 h3
      have : x = y := by linarith
      contradiction
    . have := EReal.not_ge_top x
      tauto
    . have := EReal.not_le_bottom x
      tauto
  . obtain ⟨ y, rfl ⟩ | rfl | rfl := hy
    . have := EReal.not_ge_top y
      tauto
    . contradiction
    . tauto
  . obtain ⟨ y, rfl ⟩ | rfl | rfl := hy
    . have := EReal.not_le_bottom y
      tauto
    . tauto
    . simp at h3

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := by
  have hx := EReal.def x
  have hy := EReal.def y
  have hz := EReal.def z
  obtain ⟨ x, rfl ⟩ | rfl | rfl := hx
  . obtain ⟨ y, rfl ⟩ | rfl | rfl := hy
    . obtain ⟨ z, rfl ⟩ | rfl | rfl := hz
      . simp at *
        linarith
      . simp [le_iff]
      . simp at hyz
    . obtain rfl := EReal.top_le_eq_top hyz
      exact hxy
    . simp at hxy
  . obtain rfl := EReal.top_le_eq_top hxy
    exact hyz
  . simp

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by
  rw [le_iff] at hxy
  obtain h | rfl | rfl := hxy
  . obtain ⟨ x, y, rfl, rfl, h ⟩ := h
    simp [h]
  . simp only [neg_top, EReal.bottom_le]
  . simp
    exact EReal.le_top _

/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    . simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  erw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . exact absurd hb (lt_irrefl _)
  exact ⟨↑hnon.choose, Set.mem_image_of_mem _ hnon.choose_spec, bot_lt_coe _⟩

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]
  simp
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . simp
    intro a
    norm_cast
    omega
  intro w hw
  simp
  use 0
  simp [hw]

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]
  simp
  tauto

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

example : sInf Example_6_2_8 = (0.9:ℝ) := by
  unfold Example_6_2_8
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . simp
    intro a
    norm_cast
    suffices h : (10:ℝ) ^ (-(a:ℤ) - 1) ≤ 0.1
    . linarith
    sorry
  . sorry

example : sSup Example_6_2_8 = 1 := by
  unfold Example_6_2_8
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . simp
    intro n
    norm_cast
    suffices h : (10:ℝ) ^ (-(n:ℤ) - 1) ≥ 0
    . linarith
    apply zpow_nonneg
    norm_num
  sorry

/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by
  unfold Example_6_2_9
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . simp
    intro a
    norm_cast
    omega
  . intro w hw
    use 1
    constructor
    . simp
      use 0
      norm_num
    . exact hw

example : sSup Example_6_2_9 = ⊤ := by
  unfold Example_6_2_9
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . simp
    intro a
    tauto
  . intro w wt
    obtain ⟨ x, rfl ⟩ | h | rfl := EReal.def w
    . obtain ⟨ n, hn ⟩ := exists_nat_gt x
      use n+1
      constructor
      . simp
        use n
      . norm_cast
        simp
        linarith
    . rw [lt_iff] at wt
      tauto
    . use 1
      constructor
      . simp
        use 0
        norm_num
      . tauto

theorem Ereal.sinf_empty : sInf (∅ : Set EReal) = ⊤ := by
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . simp
  . simp [le_iff]

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E := by
  rw [le_sSup_iff]
  intro b hb
  simp [upperBounds] at hb
  exact hb hx

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : sInf E ≤ x := by
  rw [sInf_le_iff]
  intro b hb
  simp [lowerBounds] at hb
  exact hb hx

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor
  . intro h
    contrapose! h
    obtain ⟨ x, hx ⟩ := h
    have h1 : sInf E ≤ x
    . exact EReal.mem_ge_inf E hx
    have h2 : x ≤ sSup E
    . exact EReal.mem_le_sup E hx
    exact EReal.trans h1 h2
  . intro rfl
    rw [Ereal.sinf_empty, EReal.sup_of_empty]
    tauto

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M := by
  rw [sSup_le_iff]
  exact hM

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_upper (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) : sInf E ≥ M := by
  rw [ge_iff_le, le_sInf_iff]
  exact hM

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib {name}`EReal`.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by
  intro a b h
  match a with
  | neg_infty =>
    match b with
    | neg_infty => rfl
    | real x =>
      simp at h
    | infty =>
      simp [toEReal] at h
      contradiction
  | real x =>
    match b with
    | neg_infty =>
      simp at h
    | real y =>
      simp at h
      suffices h : x = y
      . rw [h]
      replace h := _root_.Real.equivCut.symm.injective h
      exact Real.equivCut.injective h
    | infty =>
      simp at h
  | infty =>
    match b with
    | neg_infty =>
      simp [toEReal] at h
      contradiction
    | real x =>
      simp at h
    | infty =>
      rfl

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by
  intro y
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def y
  . obtain ⟨ x, hx ⟩ := Real.equivR.surjective y
    use x
    simp [hx]
  . use infty
  . use neg_infty

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal :=
  Equiv.ofBijective toEReal (by {
    use Chapter5.ExtendedReal.coe_inj, Chapter5.ExtendedReal.coe_surj
  })
