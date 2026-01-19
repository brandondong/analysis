import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers `ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  obtain h | h | h := lt_trichotomy x 0
  . have := abs_of_neg h
    simp [this]
    symm
    rw [abs_eq (by linarith)]
    simp
  . simp [h]
  . have := abs_of_pos h
    simp [this]
    symm
    rw [abs_eq (by linarith)]
    simp

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  rw [← abs_eq_abs] -- Respect the spirit of the exercise by using the book definition?
  obtain h | h | h := lt_trichotomy x 0
  . have := abs_of_neg h
    simp [this]
    linarith
  . simp [h, abs]
  . have := abs_of_pos h
    simp [this]
    linarith

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by
  rw [← abs_eq_abs]
  constructor <;> intro hx
  . obtain h | h | h := lt_trichotomy x 0
    . have := abs_of_neg h
      simp [this] at hx
      linarith
    . exact h
    . have := abs_of_pos h
      simp [this] at hx
      linarith
  . simp [hx]

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  simp only [← abs_eq_abs]
  -- Cases everywhere :(
  have hy := lt_trichotomy y 0
  by_cases hy2 : y = 0
  . simp [hy2, abs]
  replace hy : y < 0 ∨ 0 < y := by tauto
  obtain hx | hx | hx := lt_trichotomy x 0
  . have hxa := abs_of_neg hx
    simp only [hxa]
    obtain hy | hy := hy
    . have hya := abs_of_neg hy
      simp only [hya]
      have : x + y < 0 := by linarith
      have h := abs_of_neg this
      simp [h]
    . have hya := abs_of_pos hy
      simp only [hya]
      obtain h | h | h := lt_trichotomy (x+y) 0
      . have h2 := abs_of_neg h
        simp [h2]
        linarith
      . simp [h, abs]
        linarith
      . have h2 := abs_of_pos h
        simp [h2]
        linarith
  . simp [hx, abs]
  . have hxa := abs_of_pos hx
    simp only [hxa]
    obtain hy | hy := hy
    . have hya := abs_of_neg hy
      simp only [hya]
      obtain h | h | h := lt_trichotomy (x+y) 0
      . have h2 := abs_of_neg h
        simp [h2]
        linarith
      . simp [h, abs]
        linarith
      . have h2 := abs_of_pos h
        simp [h2]
        linarith
    . have hya := abs_of_pos hy
      simp only [hya]
      have : 0 < x + y := by linarith
      simp [abs, this]

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  simp only [← abs_eq_abs]
  obtain h | h | h := lt_trichotomy x 0
  . have h2 := abs_of_neg h
    simp [h2]
    constructor <;> intro h3
    . linarith
    . constructor
      . linarith
      . linarith
  . simp [h, abs]
  . have h2 := abs_of_pos h
    simp [h2]
    intro h3
    linarith

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  simp only [← abs_eq_abs]
  obtain h | h | h := lt_trichotomy x 0
  . have h2 := abs_of_neg h
    simp [h2]
    linarith
  . simp [h, abs]
  . have h2 := abs_of_pos h
    simp [h2]
    linarith

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  simp only [← abs_eq_abs]
  -- Just like addition, need to brute force trichotomy...
  have hx := lt_trichotomy x 0
  have hy := lt_trichotomy y 0
  by_cases hx2 : x = 0
  . simp [hx2]
  replace hx : x < 0 ∨ 0 < x := by tauto
  by_cases hy2 : y = 0
  . simp [hy2]
  replace hy : y < 0 ∨ 0 < y := by tauto
  clear hx2 hy2
  obtain hx | hx := hx <;> obtain hy | hy := hy
  . have hx2 := abs_of_neg hx
    have hy2 := abs_of_neg hy
    simp only [hx2, hy2]
    have : x * y > 0 := by exact mul_pos_of_neg_of_neg hx hy
    have := abs_of_pos this
    simp [this]
  . have hx2 := abs_of_neg hx
    rw [← gt_iff_lt] at hy
    have hy2 := abs_of_pos hy
    simp only [hx2, hy2]
    have : x * y < 0 := by exact mul_neg_of_neg_of_pos hx hy
    have := abs_of_neg this
    simp [this]
  . rw [← gt_iff_lt] at hx
    have hx2 := abs_of_pos hx
    have hy2 := abs_of_neg hy
    simp only [hx2, hy2]
    have : x * y < 0 := by exact mul_neg_of_pos_of_neg hx hy
    have := abs_of_neg this
    simp [this]
  . rw [← gt_iff_lt] at hx hy
    have hx2 := abs_of_pos hx
    have hy2 := abs_of_pos hy
    simp only [hx2, hy2]
    have : x * y > 0 := by exact Left.mul_pos hx hy
    have := abs_of_pos this
    simp [this]

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  simp only [← abs_eq_abs]
  obtain h | h | h := lt_trichotomy x 0
  . have h2 := abs_of_neg h
    have : -x > 0 := by linarith
    have h3 := abs_of_pos this
    simp only [h2, h3]
  . simp [h]
  . have h2 := abs_of_pos h
    have : -x < 0 := by linarith
    have h3 := abs_of_neg this
    simp [h3, h2]

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by
  simp only [dist]
  exact abs_nonneg (x-y)

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  simp only [dist, ← abs_eq_abs]
  constructor <;> intro h
  . obtain hxy | hxy | hxy := lt_trichotomy (x-y) 0
    . have h2 := abs_of_neg hxy
      linarith
    . linarith
    . have h2 := abs_of_pos hxy
      linarith
  . simp [h]

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  simp [dist, ← abs_eq_abs]
  obtain hxy | hxy | hxy := lt_trichotomy (x-y) 0
  . have h := abs_of_neg hxy
    simp only [h]
    have : y - x > 0 := by linarith
    have := abs_of_pos this
    simp [this]
  . have : y - x = 0 := by linarith
    simp [hxy, this]
  . rw [← gt_iff_lt] at hxy
    have h := abs_of_pos hxy
    simp only [h]
    have : y - x < 0 := by linarith
    have := abs_of_neg this
    simp [this]

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  simp [dist]
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact abs_add (x-y) (y-z)

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff, ← abs_eq_abs]
  have : (0.99:ℚ) - 1.01 < 0 := by linarith
  have := abs_of_neg this
  simp only [this]
  linarith

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff, ← abs_eq_abs]
  have : (0.99:ℚ) - 1.01 < 0 := by linarith
  have := abs_of_neg this
  simp [this]
  linarith

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [close_iff, ← abs_eq_abs]
  simp [abs]
  linarith

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  rw [close_iff, ← abs_eq_abs]
  simp [abs]

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor <;> intro h
  . simp only [h, close_iff, ← abs_eq_abs]
    intro e he
    simp [abs]
    linarith
  . contrapose! h
    by_cases hxy : x < y
    . use (y - x) / 2, (by linarith)
      rw [close_iff, ← abs_eq_abs]
      have : x - y < 0 := by linarith
      have := abs_of_neg this
      simp [this]
      linarith
    . replace hxy : x > y
      . simp [le_iff_eq_or_lt] at hxy
        obtain hxy | hxy := hxy
        . simp [hxy] at h
        . linarith
      use (x - y) / 2, (by linarith)
      rw [close_iff, ← abs_eq_abs]
      have : x - y > 0 := by linarith
      have := abs_of_pos this
      simp [this]
      linarith

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  simp only [close_iff]
  have : y - x = (-(x - y)) := by ring
  rw [this, abs_neg]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
  simp only [close_iff, ← dist_eq] at *
  have := dist_le x y z
  linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
  simp only [close_iff] at *
  have : x + z - (y + w) = (x - y) + (z - w) := by ring
  rw [this]
  have := abs_add (x-y) (z-w)
  linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
  simp only [close_iff] at *
  have : x - z - (y - w) = x - y + -(z - w) := by ring
  rw [this]
  have := abs_add (x-y) (-(z-w))
  have : |(-(z - w))| = |((z - w))| := by exact abs_neg (z - w)
  linarith

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by
  simp only [close_iff] at *
  linarith

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  simp only [close_iff, ← abs_eq_abs] at *
  have h1 := lt_trichotomy (x-w) 0
  have he : 0 ≤ ε
  . have : abs (x - y) ≥ 0
    . rw [abs_eq_abs]
      exact abs_nonneg (x-y)
    linarith
  by_cases h2 : x-w = 0
  . simp [h2, abs, he]
  replace h1 : x - w < 0 ∨ x - w > 0 := by tauto
  clear h2
  obtain h | h := hbetween <;> obtain h1 | h1 := h1
  . rw [abs_of_neg h1]
    have : x - z < 0 := by linarith
    rw [abs_of_neg this] at hxz
    linarith
  . rw [abs_of_pos h1]
    have : x - y > 0 := by linarith
    rw [abs_of_pos this] at hxy
    linarith
  . rw [abs_of_neg h1]
    have : x - y < 0 := by linarith
    rw [abs_of_neg this] at hxy
    linarith
  . rw [abs_of_pos h1]
    have : x - z > 0 := by linarith
    rw [abs_of_pos this] at hxz
    linarith

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
  simp only [close_iff] at *
  have : x * z - y * z = (x - y) * z := by ring
  rw [this]
  have := abs_mul (x - y) z
  rw [this]
  have := abs_nonneg (x-y)
  have := abs_nonneg z
  exact mul_le_mul_of_nonneg_right hxy this

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
  simp only [close_iff] at *
  have : x * z - y * w = (x-y)*z + (z- w)*y := by ring
  rw [this]; clear this
  have h1 := abs_mul (x - y) z
  have h2 := abs_mul (z - w) y
  have := abs_add ((x - y)*z) ((z - w)*y)
  rw [h1, h2] at this
  have : |x - y| * |z| ≤ ε * |z|
  . have : 0 ≤ |z| := by exact abs_nonneg z
    exact mul_le_mul_of_nonneg_right hxy this
  have : |z - w| * |y| ≤ δ * |y|
  . have : 0 ≤ |y| := by exact abs_nonneg y
    exact mul_le_mul_of_nonneg_right hzw this
  linarith

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' m with m IH
  . simp
  calc
    x ^ n * x ^ (m + 1) = x ^ n * (x ^ m * x) := by rw [pow_succ]
    _ = x ^ n * x ^ m * x := by ring
    _ = x ^ (n + m) * x := by rw [IH]
    _ = x ^ (n + m + 1) := by rw [pow_succ]
    _ = _ := by ring

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m IH
  . simp
  calc
    (x ^ n) ^ (m + 1) = (x ^ n) ^ m * (x ^ n) := by rw [pow_succ]
    _ = x ^ (n * m) * (x ^ n) := by rw [IH]
    _ = x ^ (n * m + n) := by rw [pow_add]
    _ = _ := by ring

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n IH
  . simp
  calc
    (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by rw [pow_succ]
    _ = (x ^ n * y ^ n) * (x * y) := by rw [IH]
    _ = (x ^ n * x) * (y ^ n * y) := by ring
    _ = _ := by rw [pow_succ, pow_succ]

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor <;> intro h
  . clear hn
    contrapose! h
    induction' n with n IH
    . simp
    rw [pow_succ]
    exact (mul_ne_zero_iff_right h).mpr IH
  . simp only [h]
    match n with
    | 0 =>
      linarith
    | n + 1 =>
      simp

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n IH
  . simp
  rw [pow_succ]
  exact Rat.mul_nonneg IH hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n IH
  . simp
  rw [pow_succ]
  exact Left.mul_pos IH hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n IH
  . simp
  simp [pow_succ]
  have hx : x ≥ 0 := by linarith
  have hxn : x^n ≥ 0 := pow_nonneg n hx
  have hyn : y^n ≥ 0 := pow_nonneg n hy
  exact mul_le_mul_of_nonneg IH hxy hyn hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  match n with
  | 0 => linarith
  | i + 1 =>
    clear hn n
    induction' i with i IH
    . simp
      omega
    rw [pow_succ]
    have : y ^ (i + 1 + 1) = y ^ (i + 1) * y := by rw [pow_succ]
    rw [this]
    have hx : x > 0 := by linarith
    rw [gt_iff_lt]
    apply mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
    . linarith
    . linarith
    . linarith
    . have := pow_pos (i+1) hx
      linarith

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n IH
  . simp
  rw [pow_succ, IH, ← abs_mul, pow_succ]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  match n with
  | .ofNat n => {
    simp
    induction' n with n IH
    . simp
    calc
      x ^ (n + 1) * x ^ m = (x ^ n * x) * x ^ m := by rw [pow_succ]
      _ = x ^ n * x ^ m * x := by ring
      _ = x ^ (↑n + m) * x := by rw [IH]
      _ = x ^ (↑n + m + 1) := by rw [zpow_add_one₀ hx _]
      _ = _ := by {
        simp
        ring_nf
      }
  }
  | .negSucc n => {
    simp
    induction' n with n IH
    . simp
      -- zpow_sub_one₀
      have : -1 + m = m - 1 := by ring
      rw [this, zpow_sub_one₀ hx]
      ring
    rw [pow_succ]
    have : (x ^ (n + 1) * x)⁻¹ * x ^ m = (x ^ (n + 1))⁻¹ * x ^ m * x⁻¹ := by ring
    rw [this, IH, ← zpow_sub_one₀ hx]
    have : Int.negSucc n + m - 1 = Int.negSucc (n + 1) + m
    . omega
    simp [this]
  }

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) (hx: x ≠ 0) : (x^n)^m = x^(n*m) := by
  match m with
  | .ofNat m => {
    simp
    induction' m with m IH
    . simp
    rw [pow_succ, IH, zpow_add _ _ _ hx]
    have : n * ↑m + n = n * ↑(m + 1)
    . simp
      linarith
    simp [this]
  }
  | .negSucc m =>
    simp
    induction' m with m IH
    . simp
    rw [pow_succ]
    have : ((x ^ n) ^ (m + 1) * x ^ n)⁻¹ = ((x ^ n) ^ (m + 1))⁻¹ *  (x ^ n)⁻¹ := by ring
    rw [this, IH]
    have : (x ^ n)⁻¹ = (x ^ (-n)) := by exact Eq.symm (_root_.zpow_neg x n)
    rw [this, zpow_add _ _ _ hx]
    have : n * Int.negSucc m + -n = n * Int.negSucc (m + 1)
    . have : Int.negSucc (m + 1) = Int.negSucc m - 1
      . omega
      rw [this]
      linarith
    simp [this]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) (_hx: x ≠ 0) (_hy: y ≠ 0) : (x*y)^n = x^n * y^n := by
  match n with
  | .ofNat n =>
    simp
    exact mul_pow x y n
  | .negSucc n =>
    simp
    induction' n with n IH
    . simp
      linarith
    rw [pow_succ]
    have : ((x * y) ^ (n + 1) * (x * y))⁻¹ = ((x * y) ^ (n + 1))⁻¹ * (x * y)⁻¹ := by ring
    rw [this, IH]
    have : (x ^ (n + 1))⁻¹ * (y ^ (n + 1))⁻¹ * (x * y)⁻¹ = ((x ^ (n + 1)) * x)⁻¹ * ((y ^ (n + 1)) * y)⁻¹ := by ring
    rw [this, ← pow_succ, ← pow_succ]

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by sorry

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by sorry

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  sorry

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  sorry

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by sorry

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by sorry
