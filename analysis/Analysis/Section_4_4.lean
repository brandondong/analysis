import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  -- For a/b, consider floor(a/b).
  -- We need to show inductively this value exists and has b*x+r = a.
  apply existsUnique_of_exists_of_unique
  . have hb := Rat.den_ne_zero x
    have he : ∀ a:ℤ, ∃ z:ℤ, ∃ r:ℕ, x.den * z + r = a ∧ r < x.den
    . set b := x.den
      intro a
      match a with
      | .ofNat a =>
        simp
        induction' a with a IH
        . use 0, 0
          simp
          omega
        obtain ⟨ z, r, h1, h2 ⟩ := IH
        by_cases h3 : r + 1 = b
        . use (z+1), 0
          simp
          constructor
          . linarith
          . omega
        . use z, r+1
          constructor
          . simp
            linarith
          . omega
      | .negSucc a =>
        induction' a with a IH
        . use -1, b-1
          omega
        obtain ⟨ z, r, h1, h2 ⟩ := IH
        by_cases h3 : r = 0
        . use (z-1), b-1
          constructor
          . simp [h3] at h1
            ring_nf
            omega
          . omega
        . use z, r-1
          constructor <;> omega
    obtain ⟨ z, r, h1, h2 ⟩ := he x.num
    use z
    rw [← Rat.mkRat_one, ← Rat.mkRat_self x]
    constructor
    . rw [le_iff_exists_nonneg_add]
      use mkRat r x.den
      constructor
      . rw [mkRat_nonneg_iff _ hb]
        omega
      rw [Rat.mkRat_add_mkRat _ _ (by omega) hb, Rat.mkRat_eq_iff (by omega) hb]
      simp
      linarith
    . rw [lt_iff_exists_pos_add]
      use mkRat (x.den - r) x.den
      constructor
      . rw [Rat.mkRat_pos_iff _ hb]
        linarith
      have : mkRat 1 1 = 1 := by rfl
      rw [← this]; clear this
      rw [Rat.mkRat_add_mkRat_of_den _ _ hb, Rat.mkRat_add_mkRat_of_den _ _ (by omega)]
      rw [Rat.mkRat_eq_iff hb (by omega)]
      simp
      linarith
  . intro n1 n2 hn1 hn2
    by_contra hn
    -- wlog, n1 < n2. Then n1+1 <= n2.
    wlog h : n1 < n2
    . replace h : n2 < n1 := by omega
      exact this x n2 n1 hn2 hn1 (by tauto) h
    replace h : n1+1 ≤ n2 := by omega
    replace h : (n1:ℚ) +1 ≤ n2
    . norm_cast
    linarith

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  obtain h | h := lt_or_ge x 0
  . use 0
    linarith
  obtain ⟨ n, ⟨ _, hn ⟩, _ ⟩ := Rat.between_int x
  match n with
  | .ofNat n =>
    use (n+1)
    simp at hn
    norm_cast at hn
  | .negSucc n =>
    have : ((Int.negSucc n):ℚ) ≤ -1
    . norm_cast
      omega
    linarith

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  intro ⟨ a, h ⟩
  -- Show for any value below a, there exists n where a n <= that value.
  have goal : ∀ y:ℕ, ∃ n:ℕ, (a n) + y ≤ a 0
  . intro y
    induction' y with y IH
    . use 0
      omega
    obtain ⟨ n, IH ⟩ := IH
    specialize h n
    use n+1
    omega
  obtain ⟨ n, hn ⟩ := goal (a 0 + 1)
  omega

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use fun n ↦ -n
  intro n
  simp

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use fun n ↦ ⟨ mkRat 1 (2^n), by {
    apply Rat.mkRat_pos
    . omega
    . norm_num
  }⟩
  intro n
  simp
  rw [lt_iff_exists_pos_add]
  use mkRat 1 (2 ^ (n + 1))
  have h : 2 ^ (n + 1) ≠ 0 := by simp
  have h2 : 2 ^ (n + 1) * 2 ^ (n + 1) ≠ 0
  . contrapose! h
    simp at h
  have h3 : 2 ^ n ≠ 0 := by omega
  constructor
  . apply Rat.mkRat_pos
    . omega
    . exact h
  . rw [Rat.mkRat_add_mkRat _ _ h h, Rat.mkRat_eq_iff h2 h3]
    simp
    ring

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  induction' n with n IH
  . left
    rw [even_iff_exists_two_mul]
    use 0
    ring
  obtain h | h := IH
  . right
    rw [even_iff_exists_two_mul] at h
    rw [odd_iff_exists_bit1]
    obtain ⟨ x, hx ⟩ := h
    use x
    omega
  . left
    rw [even_iff_exists_two_mul]
    rw [odd_iff_exists_bit1] at h
    obtain ⟨ x, hx ⟩ := h
    use x+1
    omega

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  intro ⟨ he, ho ⟩
  rw [even_iff_exists_two_mul] at he
  rw [odd_iff_exists_bit1] at ho
  obtain ⟨ x, hx ⟩ := he
  obtain ⟨ y, hy ⟩ := ho
  have h : 2 * (x + y) = 1 := by omega
  obtain h | h | h := lt_trichotomy (x+y) 1 <;> omega

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . by_contra contra
        simp at contra
        have h1 : q ^ 2 ≥ 4 * k ^ 2
        . have : q ^ 2 = q * q := by ring
          rw [this]
          have : 4 * k ^ 2 = (2 * k) * (2 * k) := by ring
          rw [this]
          exact Nat.mul_le_mul contra contra
        have h2 : k > 0
        . by_contra hk
          replace hk : k = 0 := by omega
          simp [hk] at this
          omega
        rw [this] at h1
        have h3 : k ^ 2 > 0
        . exact Nat.pow_pos h2
        linarith
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      rw [odd_iff_exists_bit1] at hp
      obtain ⟨ x, rfl ⟩ := hp
      rw [odd_iff_exists_bit1]
      use 2*x^2 + 2*x
      ring
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
