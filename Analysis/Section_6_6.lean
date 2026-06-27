import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by
  use fun x ↦ 2 * x
  constructor
  . intro n1 n2 hn
    simp [hn]
  simp

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := by
  intro n1 n2 h
  contrapose! h
  wlog hn : n1 < n2
  . have := this hf (n1 := n2) (n2 := n1) (by omega) (by omega)
    omega
  specialize hf hn
  omega

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := by
  use fun x ↦ x
  constructor
  . intro n1 n2 h
    simp [h]
  simp

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by
  unfold Sequence.subseq at *
  obtain ⟨ f, hfm, hf ⟩ := hab
  obtain ⟨ g, hgm, hg ⟩ := hbc
  use f ∘ g
  constructor
  . intro n1 n2 hn
    specialize hgm hn
    specialize hfm hgm
    simp [hfm]
  intro n
  specialize hg n
  rw [hg]
  specialize hf (g n)
  simp [hf]

theorem Sequence.tendsTo_coe (a:ℕ → ℝ) (L:ℝ) :
  (a:Sequence).TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
  rw [Sequence.tendsTo_iff]
  constructor <;> intro h
  . intro e he
    specialize h e he
    obtain ⟨ N, hN ⟩ := h
    use (max N 0).toNat
    intro n hn
    simp at hn
    specialize hN n hn
    simp at hN
    exact hN
  . intro e he
    specialize h e he
    obtain ⟨ N, hN ⟩ := h
    use N
    intro n hn
    have hn2 : n ≥ 0 := by omega
    lift n to ℕ using hn2
    simp at hn
    specialize hN n hn
    simp [hN]

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  constructor <;> intro h
  . intro b hb
    rw [Sequence.tendsTo_coe] at *
    obtain ⟨ f, hfm, hf ⟩ := hb
    intro e he
    specialize h e he
    obtain ⟨ N, hN ⟩ := h
    use N
    intro n hn
    specialize hf n
    rw [hf]
    specialize hN (f n) (by {
      have hfn : f N ≥ N := by exact StrictMono.le_apply hfm
      have hfn2 : f n ≥ f N := by exact (StrictMono.le_iff_le hfm).mpr hn
      omega
    })
    exact hN
  . apply h
    exact subseq_self a

theorem Sequence.limit_point_coe (a:ℕ → ℝ) (x:ℝ) :
  (a:Sequence).LimitPoint x ↔ ∀ ε > 0, ∀ N, ∃ n ≥ N, |a n - x| ≤ ε := by
  rw [limit_point_def]
  constructor <;> intro h
  . intro e he N
    specialize h e he N (by simp)
    obtain ⟨ n, hn, h ⟩ := h
    have hn2 : n ≥ 0 := by omega
    lift n to ℕ using hn2
    simp at hn
    simp at h
    use n
  . intro e he N hN
    simp at hN
    lift N to ℕ using hN
    specialize h e he N
    obtain ⟨ n, hn, h ⟩ := h
    use n, (by simp [hn])
    simp [h]

noncomputable abbrev limit_point_subseq_func {a:ℕ → ℝ} {L:ℝ} (h: (a:Sequence).LimitPoint L) : ℕ → ℕ :=
  fun n ↦
    let h1 := (Sequence.limit_point_coe a L).mp h
    match n with
    | 0 => 0
    | Nat.succ n =>
      let y := limit_point_subseq_func h n
      (h1 (1/(n+1)) (Nat.one_div_pos_of_nat) (y+1)).choose

theorem limit_point_subseq_func_mono {a:ℕ → ℝ} {L:ℝ} (h: (a:Sequence).LimitPoint L) : StrictMono (limit_point_subseq_func h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  set y := limit_point_subseq_func h n
  simp only [limit_point_subseq_func]
  set c := limit_point_subseq_func._proof_3 h n
  have hc := c.choose_spec
  simp only [y]
  omega

theorem limit_point_subseq_func_close {a:ℕ → ℝ} {L:ℝ} (h: (a:Sequence).LimitPoint L) (n: ℕ) : |a (limit_point_subseq_func h (n + 1)) - L| ≤ 1 / ((n:ℝ) + 1) := by
  simp only [limit_point_subseq_func]
  set c := limit_point_subseq_func._proof_3 h n
  have hc := c.choose_spec
  exact hc.2

theorem limit_point_subseq_func_le {a:ℕ → ℝ} {L:ℝ} (h: (a:Sequence).LimitPoint L) (n: ℕ) : ∀ m ≥ n, |a (limit_point_subseq_func h (m + 1)) - L| ≤ 1 / ((n:ℝ) + 1) := by
  intro m hm
  have h1 := limit_point_subseq_func_close h m
  have h2 : 1 / ((m:ℝ) + 1) ≤ 1 / (n + 1)
  . simp [le_iff_exists_add] at hm
    obtain ⟨ c, rfl ⟩ := hm
    field_simp
    simp
  linarith

/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  constructor <;> intro h
  . set f:ℕ → ℕ := limit_point_subseq_func h
    use fun n ↦ a (f n)
    constructor
    . simp [subseq]
      use f
      simp [f, limit_point_subseq_func_mono]
    rw [tendsTo_coe]
    intro e he
    simp only [f]
    obtain ⟨ n, hn ⟩ : ∃ n:ℕ, 1 / ((n:ℝ) + 1) ≤ e
    . obtain ⟨ n, hn ⟩ := exists_nat_gt (1/e)
      use n
      field_simp at ⊢ hn
      linarith
    use n+1
    intro m hm
    have hm2 : m > 0 := by omega
    simp [← Nat.exists_add_one_eq] at hm2
    obtain ⟨ m, rfl ⟩ := hm2
    simp at hm
    have h1 := limit_point_subseq_func_le h n m hm
    linarith
  . obtain ⟨ b, hab, hb ⟩ := h
    rw [Sequence.tendsTo_coe] at hb
    obtain ⟨ f, hfm, hf ⟩ := hab
    -- a (f n) converges to L.
    rw [limit_point_coe]
    intro e he N
    specialize hb e he
    obtain ⟨ M, hM ⟩ := hb
    specialize hM (max M N) (by simp)
    specialize hf (max M N)
    rw [hf] at hM
    use (f (max M N)), (by {
      have h1 : f (max M N) ≥ f N
      . have h1 : (max M N) ≥ N := by simp
        exact (StrictMono.le_iff_le hfm).mpr h1
      have h2 : f N ≥ N := by exact StrictMono.le_apply hfm
      omega
    })

/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isTrue
  use fun n ↦ if Even n then 0 else 1
  use fun n ↦ if Odd n then 0 else 1
  have hf : (StrictMono fun n ↦ n + 1)
  . intro n1 n2 h
    simp [h]
  split_ands
  . simp [funext_iff]
    use 0
    simp
  . use fun n ↦ n+1, hf
    intro n
    simp
    by_cases h : Odd n
    . simp [h]
    . simp [h]
      exact Nat.odd_add_one.mpr h
  . use fun n ↦ n+1, hf
    intro n
    simp
    by_cases h : Even n
    . simp [h]
    . simp [h]
      exact Nat.even_add_one.mpr h

lemma Sequence.boundedBy_def_coe {a:ℕ → ℝ} {M:ℝ} (hM: M ≥ 0) :
  (a:Sequence).BoundedBy M ↔ ∀ n, |a n| ≤ M := by
  rw [Sequence.boundedBy_def]
  constructor <;> intro h
  . intro n
    specialize h n
    simp at h
    exact h
  . intro n
    by_cases hn : 0 ≤ n
    . lift n to ℕ using hn
      specialize h n
      simp [h]
    . simp [hn, hM]

theorem unbounded_n_helper {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) (n:ℕ) (r:ℝ) : ∃ n'>n, |a n'| > r := by
  simp only [Sequence.isBounded_def] at ha
  contrapose! ha
  obtain ⟨ M, hM ⟩ := Sequence.finite_bounded_helper a (n+1) (by simp; omega)
  use max (max M r) 0, (by simp)
  rw [Sequence.boundedBy_def_coe (by simp)]
  intro m
  obtain hm | hm := lt_or_ge m (n+1)
  . specialize hM m (by omega)
    simp at hM
    simp [hM]
  . specialize ha m (by omega)
    simp [ha]

noncomputable abbrev unbound_n_func {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) : ℕ → ℕ :=
  fun n ↦
    match n with
    | 0 =>
      (unbounded_n_helper ha 0 0).choose
    | Nat.succ n =>
      let y := unbound_n_func ha n
      let z := (unbounded_n_helper ha y (n+1))
      z.choose

theorem unbound_n_func_mono {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) : StrictMono (unbound_n_func ha) := by
  apply strictMono_nat_of_lt_succ
  intro n
  set y := unbound_n_func ha n
  simp only [unbound_n_func]
  set c := unbound_n_func._proof_3 ha n
  have hc := c.choose_spec
  unfold y
  exact hc.1

theorem unbound_n_func_lt {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) (n:ℕ) : |a (unbound_n_func ha n)| > n := by
  match n with
  | 0 =>
    simp only [unbound_n_func]
    set c := unbound_n_func._proof_1 ha
    have hc := c.choose_spec
    have : (0:ℕ) = (0:ℝ) := by norm_num
    rw [this]
    exact hc.2
  | Nat.succ n =>
    simp only [unbound_n_func]
    set c := unbound_n_func._proof_3 ha n
    have hc := c.choose_spec
    simp [hc.2]

/--
  Exercise 6.6.3.  You may find the API around Mathlib's {name}`Nat.find` to be useful
  (and {syntax command}`open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  -- If a is unbounded, then for any n r, there exists n' > n where |a n'| > r.
  -- Set f n as this number for f (n-1), r=n.
  -- 1/(b n) = 1/(a f n) < 1/n.
  use fun n ↦ a (unbound_n_func ha n)
  constructor
  . simp [subseq]
    use unbound_n_func ha
    simp [unbound_n_func_mono]
  rw [Sequence.inv_coe, tendsTo_coe]
  intro e he
  obtain ⟨ n, hn ⟩ := exists_nat_gt (1/e)
  replace hn : 1/(n+1) < e
  . field_simp at ⊢ hn
    linarith
  use n+1
  intro m hm
  simp
  rw [ge_iff_le, le_iff_exists_nonneg_add] at hm
  obtain ⟨ c, _, rfl ⟩ := hm
  have h1 := unbound_n_func_lt ha (n+1+c)
  have h2 : |a (unbound_n_func ha (n + 1 + c))|⁻¹ < 1/((n + 1 + c):ℕ)
  . have : |a (unbound_n_func ha (n + 1 + c))| > 0
    . linarith
    field_simp
    exact h1
  have h3 : 1/((n + 1 + c):ℕ) ≤ e
  . field_simp at ⊢ hn
    simp
    have : e * (↑n + 1) ≤ e * (↑n + 1 + ↑c)
    . apply mul_le_mul_of_nonneg_left
      . linarith
      . linarith
    linarith
  linarith


end Chapter6
