import Mathlib.Tactic

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 7.1: Finite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Technical note: it is convenient in Lean to extend finite sequences (usually by zero) to be
functions on the entire integers.

Main constructions and results of this section:
-/

-- This makes available the convenient notation `∑ n ∈ A, f n` to denote summation of `f n` for
-- `n` ranging over a finite set `A`.
open BigOperators

/-!
- API for summation over finite sets (encoded using Mathlib's {name}`Finset` type), using the
  {name}`Finset.sum` method and the `∑ n ∈ A, f n` notation.
- Fubini's theorem for finite series

We do not attempt to replicate the full API for {name}`Finset.sum` here, but in subsequent sections we
shall make liberal use of this API.

-/

-- This is a technical device to avoid Mathlib's insistence on decidable equality for finite sets.
open Classical

namespace Finset

-- We use `Finset.Icc` to describe finite intervals in the integers. `Finset.mem_Icc` is the
-- standard Mathlib tool for checking membership in such intervals.
#check mem_Icc

/-- Definition 7.1.1 -/
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

/--
  Definition 7.1.1. This is similar to Mathlib's {name}`Finset.sum_Icc_succ_top` except that the
  latter involves summation over the natural numbers rather than integers.
-/
theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by
  apply sum_eq_zero
  intro x hx
  simp at hx

theorem sum_of_m_m_sub_one (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by
  apply sum_eq_zero
  intro x hx
  simp at hx

theorem sum_of_m_m (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by
  apply sum_eq_single_of_mem
  . simp
  intro b hb h
  simp at hb
  contradiction

theorem sum_of_m_m_add_one (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  rw [sum_of_nonempty (by omega), sum_of_m_m]

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have hm : m+2 = (m+1)+1 := by ring
  rw [hm, sum_of_nonempty (by omega), sum_of_m_m_add_one]

/-- Remark 7.1.3 -/
example (a: ℤ → ℝ) (m n:ℤ) : ∑ i ∈ Icc m n, a i = ∑ j ∈ Icc m n, a j := rfl

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  rw [le_iff_exists_nonneg_add] at hpn
  obtain ⟨ c, hc, rfl ⟩ := hpn
  lift c to ℕ using hc
  induction' c with c IH
  . simp only [CharP.cast_eq_zero, add_zero]
    have : (∑ i ∈ Icc (n + 1) n, a i) = 0
    . apply sum_of_empty
      omega
    linarith
  have : n + ((c + 1):ℕ) = (n + c) + 1 := by omega
  rw [this]; clear this
  rw [sum_of_nonempty (by omega), sum_of_nonempty (by omega)]
  linarith

/-- Lemma 7.1.4(b) / Exercise 7.1.1 -/
theorem shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  obtain h | h := lt_or_ge n m
  . rw [sum_of_empty h, sum_of_empty (by omega)]
  rw [le_iff_exists_nonneg_add] at h
  obtain ⟨ c, hc, rfl ⟩ := h
  lift c to ℕ using hc
  induction' c with c IH
  . simp
  have : m + ((c + 1):ℕ) = (m + c) + 1 := by omega
  rw [this]; clear this
  rw [sum_of_nonempty (by omega), IH]; clear IH
  have : m + c + 1 + k = m + c + k + 1 := by ring
  rw [this, sum_of_nonempty (by omega)]; clear this
  have : m + ↑c + k + 1 - k = m + ↑c + 1 := by ring
  rw [this]

theorem eq_finite_series {m n:ℤ} {a b: ℤ → ℝ} (h: ∀ (i:ℤ), m ≤ i ∧ i ≤ n → a i = b i) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc m n, b i := by
  obtain hnm | hnm := lt_or_ge n m
  . simp [sum_of_empty hnm]
  rw [le_iff_exists_nonneg_add] at hnm
  obtain ⟨ c, hc, rfl ⟩ := hnm
  lift c to ℕ using hc
  induction' c with c IH
  . simp
    exact h m (by simp)
  specialize IH (by {
    intro i hi
    apply h
    omega
  })
  have : m + ((c + 1):ℕ) = (m + c) + 1 := by omega
  rw [this]; clear this
  rw [sum_of_nonempty (by omega), IH, sum_of_nonempty (by omega)]
  specialize h (m+c+1) (by omega)
  linarith

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_add {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
  obtain h | h := lt_or_ge n m
  . simp only [sum_of_empty h]
    norm_num
  rw [le_iff_exists_nonneg_add] at h
  obtain ⟨ c, hc, rfl ⟩ := h
  lift c to ℕ using hc
  induction' c with c IH
  . simp
  have : m + ((c + 1):ℕ) = (m + c) + 1 := by omega
  rw [this]; clear this
  rw [sum_of_nonempty (by omega), IH]; clear IH
  rw [sum_of_nonempty (by omega), sum_of_nonempty (by omega)]
  linarith

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_const_mul {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  obtain h | h := lt_or_ge n m
  . simp only [sum_of_empty h]
    ring
  rw [le_iff_exists_nonneg_add] at h
  obtain ⟨ d, hd, rfl ⟩ := h
  lift d to ℕ using hd
  induction' d with d IH
  . simp
  have : m + ((d + 1):ℕ) = (m + d) + 1 := by omega
  rw [this, sum_of_nonempty (by omega), sum_of_nonempty (by omega), IH]
  linarith

/-- Lemma 7.1.4(e) / Exercise 7.1.1 -/
theorem abs_finite_series_le {m n:ℤ} (a: ℤ → ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
  obtain h | h := lt_or_ge n m
  . simp only [sum_of_empty h]
    norm_num
  rw [le_iff_exists_nonneg_add] at h
  obtain ⟨ d, hd, rfl ⟩ := h
  lift d to ℕ using hd
  induction' d with d IH
  . simp
  have : m + ((d + 1):ℕ) = (m + d) + 1 := by omega
  rw [this, sum_of_nonempty (by omega), sum_of_nonempty (by omega)]; clear this
  have := abs_add_le (∑ i ∈ Icc m (m + ↑d), a i) (a (m + ↑d + 1))
  linarith

/-- Lemma 7.1.4(f) / Exercise 7.1.1 -/
theorem finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
  obtain h | hnm := lt_or_ge n m
  . simp only [sum_of_empty h]
    norm_num
  rw [le_iff_exists_nonneg_add] at hnm
  obtain ⟨ d, hd, rfl ⟩ := hnm
  lift d to ℕ using hd
  induction' d with d IH
  . simp
    apply h <;> omega
  specialize IH (by {
    intro i hi1 hi2
    exact h i hi1 (by omega)
  })
  have : m + ((d + 1):ℕ) = (m + d) + 1 := by omega
  rw [this, sum_of_nonempty (by omega), sum_of_nonempty (by omega)]
  specialize h (m+d+1) (by omega) (by omega)
  linarith

set_option maxHeartbeats 210000 in
/--
  Proposition 7.1.8.
-/
theorem finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :
    ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- This proof is written to broadly follow the structure of the original text.
  revert X n; intro n
  induction' n with n hn
  . simp
  intro X hX g h hg hh
  -- A technical step: we extend g, h to the entire integers using a slightly artificial map π
  set π : ℤ → Icc (1:ℤ) (n+1) :=
    fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1:ℤ) (n+1) → X) :
      ∑ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∑ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
    apply sum_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]
  simp [-mem_Icc, hπ]
  rw [sum_of_nonempty (by linarith) _]
  set x := g (π (n+1))
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  set h' : ℤ → X := fun i ↦ if (i:ℤ) < j then h (π i) else h (π (i+1))
  have : ∑ i ∈ Icc (1:ℤ) (n + 1), f (h (π i)) = ∑ i ∈ Icc (1:ℤ) n, f (h' i) + f x := calc
    _ = ∑ i ∈ Icc (1:ℤ) j, f (h (π i)) + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      symm; apply concat_finite_series <;> linarith
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f ( h (π j) )
        + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      congr; convert sum_of_nonempty _ _ <;> simp [hj1]
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f x + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]
      symm; convert shift_finite_series _; simp
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) + f x := by abel
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h' i) + ∑ i ∈ Icc (j:ℤ) n, f (h' i) + f x := by
      congr 2
      all_goals apply sum_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by linarith]
      simp [show ¬ i < j by linarith]
    _ = _ := by congr; convert concat_finite_series _ _ _ <;> linarith
  rw [this]
  congr 1
  have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g (π i) ≠ x := by
    simp at hi
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x := by
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt: i < j <;> by_contra! heq
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq
    . linarith
    contrapose! hlt; linarith
  set gtil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, g_ne_x] ⟩
  set htil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val
  have why : Function.Bijective gtil := by sorry
  have why2 : Function.Bijective htil := by sorry
  calc
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply sum_congr rfl; grind
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply sum_congr rfl; grind

/--
  This fact ensures that Definition 7.1.6 would be well-defined even if we did not appeal to the
  existing {name}`Finset.sum` method.
-/
theorem exist_bijection {n:ℕ} {Y:Type*} (X: Finset Y) (hcard: X.card = n) :
    ∃ g: Icc (1:ℤ) n → X, Function.Bijective g := by
  have := Finset.equivOfCardEq (show (Icc (1:ℤ) n).card = X.card by simp [hcard])
  exact ⟨ this, this.bijective ⟩

/-- Definition 7.1.6 -/
theorem finite_series_eq {n:ℕ} {Y:Type*} (X: Finset Y) (f: Y → ℝ) (g: Icc (1:ℤ) n → X)
  (hg: Function.Bijective g) :
    ∑ i ∈ X, f i = ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert sum_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all

/-- Proposition 7.1.11(a) / Exercise 7.1.2 -/
theorem finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by
  have h := finite_series_eq (n := 0) (Y := X') (∅) f (fun x ↦ nomatch x) (by {
    constructor
    . intro x1 x2 h
      nomatch x1
    . intro y
      nomatch y
  })
  rw [h]
  apply sum_of_empty
  norm_num

/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  have h1 : (1:ℕ)  = (1:ℤ) := by norm_num
  have h := finite_series_eq (n := 1) (Y := X') {x₀} f (fun x ↦ ⟨ x₀, by simp ⟩) (by {
    constructor
    . intro n1 n2 _
      have hn1 := n1.2
      have hn2 := n2.2
      ext
      set d1 := n1.1
      set d2 := n2.1
      simp at hn1 hn2
      rw [hn1, hn2]
    . intro y
      use ⟨ 1, by simp ⟩
      simp
      ext
      simp
      have := y.2
      symm
      set d := y.val
      simp at this
      exact this
  })
  rw [h]
  rw [h1, sum_of_m_m]
  simp

/--
  A technical lemma relating a sum over a finset with a sum over a fintype. Combines well with
  tools such as `map_finite_series` below.
-/
theorem finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, f x = ∑ x:X, f x.val := (sum_coe_sort X f).symm

/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
  -- We only know how to talk about sum of elems in Finset instead of being part of a Fintype...
  rw [finite_series_of_fintype]
  obtain ⟨ fx, hfx ⟩ := exist_bijection (n := univ.card) (Y := X) (univ) (by rfl)
  have h1 := finite_series_eq (n := univ.card) (Y := X) (univ) f fx hfx
  rw [finite_series_of_fintype] at h1
  rw [h1]; clear h1
  rw [finite_series_of_fintype (X' := Y)]
  obtain ⟨ fy, hfy ⟩ := exist_bijection (n := univ.card) (Y := Y) (univ) (by rfl)
  have h2 := finite_series_eq (n := univ.card) (Y := Y) (univ) (f ∘ g) fy hfy
  rw [finite_series_of_fintype] at h2
  rw [Function.comp_def] at h2
  rw [h2]; clear h2
  simp only [card_univ]
  have hc : Fintype.card X = Fintype.card Y
  . exact (Fintype.card_of_bijective hg).symm
  simp_rw [← hc]
  -- Use finite_series_of_rearrange.
  -- We can find two bijective mappings from Z -> X (map to X, map to g Y).
  set g' : (Icc 1 ((Fintype.card X):ℤ)) → (univ : Finset X) := fun i ↦
    let v := fy ⟨ i, (by rw [card_univ, ← hc]; simp) ⟩ ;
    let v2 := g v
    ⟨ v2, (by simp) ⟩
  have hg' : Function.Bijective g'
  . constructor
    . intro a b h
      simp [g'] at h
      replace h := hg.1 h
      simp at h
      replace h := hfy.1 h
      simp at h
      exact h
    . intro b
      simp only [g']
      obtain ⟨ a, ha ⟩ := hg.2 b
      obtain ⟨ i, hi ⟩ := hfy.2 (⟨ a, (by simp) ⟩)
      use ⟨ i, by {
        have hi := i.2
        simp_rw [card_univ, ← hc] at hi
        exact hi
      } ⟩
      simp [hi, ha]
  have := finite_series_of_rearrange (n := Fintype.card X) (X' := X) (univ) (by rfl) f fx (g') hfx hg'
  rw [this]; clear this
  simp [g']

-- Proposition 7.1.11(d) is `rfl` in our formalism and is therefore omitted.

/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
  have hc : (X ∪ Y).card = (X.card + Y.card) := card_union_of_disjoint hdisj
  obtain ⟨ fx, hfx ⟩ := exist_bijection (n := X.card) (Y := Z) (X) (by rfl)
  have := finite_series_eq (n := X.card) (Y := Z) (X) f fx hfx
  rw [this]; clear this
  obtain ⟨ fy, hfy ⟩ := exist_bijection (n := Y.card) (Y := Z) (Y) (by rfl)
  have := finite_series_eq (n := Y.card) (Y := Z) (Y) f fy hfy
  rw [this]; clear this
  -- There exists bijective f' where 1-n map to X via fx and n+1-n+m map to Y via fy.
  -- concat_finite_series + shift, then set to equal both sides of +.
  set fxy : ↥(Icc 1 (((X.card + Y.card):ℕ):ℤ)) → ↥(X ∪ Y) := fun i ↦
    if hi:i.val ≤ X.card then
      let v := fx ⟨ i, (by {
        have hi2 := i.2
        set c := i.val
        simp at hi2
        simp [hi, hi2]
      }) ⟩;
      ⟨ v, (by simp) ⟩
    else
      let v := fy ⟨ i-X.card, (by {
        have hi2 := i.2
        set c := i.val
        simp at hi2
        simp
        omega
      }) ⟩;
      ⟨ v, (by simp) ⟩
  have hfxy : Function.Bijective fxy
  . constructor
    . intro i1 i2 h
      simp [fxy] at h
      have hii : i1.val ≤ X.card ↔ i2.val ≤ X.card
      . wlog hi : i1.val ≤ X.card generalizing i1 i2
        . simp only [hi, false_iff]
          have hii := this (i1 := i2) (i2 := i1) h.symm
          by_contra hi2
          exact hi ((hii hi2).mp hi2)
        simp [hi]
        by_contra hi2
        simp [hi, hi2] at h
        have hc (x: X) (y: Y) : x.val ≠ y.val
        . by_contra h
          have hy := y.2
          rw [← h] at hy
          contrapose! hy
          have hx := x.2
          exact Disjoint.notMem_of_mem_left_finset hdisj hx
        tauto
      by_cases hi1 : i1.val ≤ X.card
      . have hi2 := hii.mp hi1
        simp [hi1, hi2] at h
        have := hfx.1 h
        simp at this
        exact this
      . simp only [hi1, false_iff] at hii
        simp [hi1, hii] at h
        have := hfy.1 h
        simp at this
        exact this
    . intro ⟨ z, hz ⟩
      simp at hz
      simp only [fxy]
      obtain hz | hz := hz
      . obtain ⟨ ⟨ i, hi ⟩, hfi ⟩ := hfx.2 ⟨ z, hz ⟩
        simp at hi
        use ⟨ i, by simp; omega ⟩
        simp [hi, hfi]
      . obtain ⟨ ⟨ i, hi ⟩, hfi ⟩ := hfy.2 ⟨ z, hz ⟩
        simp at hi
        use ⟨ i+X.card, (by simp; omega) ⟩
        have hi2 : ¬ i ≤ 0 := by omega
        simp [hi2, hfi]
  have := finite_series_eq (n := (X.card + Y.card)) (Y := Z) (X ∪ Y) f fxy hfxy
  rw [this]; clear this
  have := concat_finite_series (m := 1) (n := X.card) (p := X.card + Y.card) (by omega) (by omega)
  have hc2 : ((X.card + Y.card):ℕ) = (X.card:ℤ) + Y.card := by omega
  simp_rw [hc2];
  rw [← concat_finite_series (m := 1) (n := X.card) (p := X.card + Y.card) (by omega) (by omega)]
  have split (a b c d:ℝ) (h1: a = b) (h2: c = d) : a + c = b + d := by linarith
  apply split <;> clear split
  . apply eq_finite_series
    intro i ⟨ hi1, hi2 ⟩
    simp [hi1, hi2]
    have : i ≤ ↑(#X) + ↑(#Y) := by omega
    simp [this, fxy, hi2]
  . rw [shift_finite_series (m := 1) (n := Y.card) (k := X.card)]
    rw [add_comm]
    have hc3 : Y.card + X.card = (X.card:ℤ) + Y.card := by omega
    rw [hc3]; clear hc3
    apply eq_finite_series
    intro i ⟨ hi1, hi2 ⟩
    have h1 : 1 ≤ i ∧ i ≤ ↑(#X) + ↑(#Y) := by omega
    have h2 : 1 ≤ i - ↑(#X) ∧ i ≤ ↑(#Y) + ↑(#X) := by omega
    have h3 : ¬ i ≤ ↑(#X) := by omega
    simp [h1, h2, fxy, h3]

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
  obtain ⟨ fx, hfx ⟩ := exist_bijection (n := X.card) (Y := X') (X) (by rfl)
  have h1 := finite_series_eq (n := X.card) (Y := X') (X) f fx hfx
  have h2 := finite_series_eq (n := X.card) (Y := X') (X) g fx hfx
  have h3 := finite_series_eq (n := X.card) (Y := X') (X) (f+g) fx hfx
  rw [h1, h2, h3]; clear h1 h2 h3
  rw [← finite_series_add]
  apply eq_finite_series
  intro i hi
  have hi2 : i ∈ Icc 1 ↑(#X)
  . simp [hi]
  simp [hi2]

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
  obtain ⟨ fx, hfx ⟩ := exist_bijection (n := X.card) (Y := X') (X) (by rfl)
  have h1 := finite_series_eq (n := X.card) (Y := X') (X) f fx hfx
  have h2 := finite_series_eq (n := X.card) (Y := X') (X) (fun x ↦ c * f x) fx hfx
  rw [h1, h2]; clear h1 h2
  rw [← finite_series_const_mul]
  apply eq_finite_series
  intro i hi
  have hi2 : i ∈ Icc 1 ↑(#X)
  . simp [hi]
  simp [hi2]

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
  obtain ⟨ fx, hfx ⟩ := exist_bijection (n := X.card) (Y := X') (X) (by rfl)
  have h1 := finite_series_eq (n := X.card) (Y := X') (X) f fx hfx
  have h2 := finite_series_eq (n := X.card) (Y := X') (X) g fx hfx
  rw [h1, h2]; clear h1 h2
  apply finite_series_of_le
  intro i hi hi2
  simp [hi, hi2]
  apply h
  simp

/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by
  obtain ⟨ fx, hfx ⟩ := exist_bijection (n := X.card) (Y := X') (X) (by rfl)
  have h1 := finite_series_eq (n := X.card) (Y := X') (X) f fx hfx
  have h2 := finite_series_eq (n := X.card) (Y := X') (X) (fun x ↦ |f x|) fx hfx
  rw [h1, h2]; clear h1 h2
  have := abs_finite_series_le (m := 1) (n := X.card) (a := fun i ↦ if hi : i ∈ Icc 1 ↑(#X) then (f (fx (⟨ i, (by exact hi) ⟩))) else 0)
  have h {a b c:ℝ} (h1: a ≤ b) (h2 : b = c) : a ≤ c := by linarith
  apply h this; clear h this
  apply eq_finite_series
  intro i hi
  have hi2 : i ∈ Icc 1 ↑(#X)
  . simp [hi]
  simp [hi2]

/-- Lemma 7.1.13 --/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . intro X hX
    have hXe : X = ∅
    . exact card_eq_zero.mp hX
    rw [hXe]
    simp only [product_eq_sprod, empty_product]
    simp only [finite_series_of_empty]
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . rw [hunion]
        simp only [product_eq_sprod]
        ext ⟨ x, y ⟩
        simp
        constructor <;> intro h <;> tauto
      simp only [product_eq_sprod]
      rw [Finset.disjoint_iff_inter_eq_empty] at hdisj ⊢
      ext ⟨ x, y ⟩
      constructor <;> intro h
      . simp at h
        rw [Finset.ext_iff] at hdisj
        have := (hdisj x).mp (by {
          simp [h]
        })
        nomatch this
      . nomatch h

/-- Corollary 7.1.14 (Fubini's theorem for finite series)-/
theorem finite_series_refl {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

theorem finite_series_comm {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]


-- Exercise 7.1.3 : develop as many analogues as you can of the above theory for finite products
-- instead of finite sums.

#check Nat.factorial_zero
#check Nat.factorial_succ

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics {tactic}`zify`, {tactic}`norm_cast`, and {tactic}`omega`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  sorry

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  sorry

/-- Exercise 7.1.6 -/
theorem sum_union_disjoint {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) :
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  sorry

/-- {given}`aᵢ` Exercise 7.1.7. Uses {lean}`Fin m` (so {lean}`aᵢ < m`) instead of the book's {lean}`aᵢ ≤ m`;
  the bound is baked into the type, and {kw (of := «term_<_»)}`<` replaces {kw (of := «term_≤_»)}`≤` to match the 0-indexed shift. -/
theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  sorry

end Finset
