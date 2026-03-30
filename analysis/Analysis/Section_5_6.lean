import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from `Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' m with m IH
  . simp
  calc
    _ = x ^ n * (x ^ m * x) := by rw [pow_succ]
    _ = (x ^ n * x ^ m) * x := by ring
    _ = x ^ (n + m) * x := by rw [IH]
    _ = x ^ (n + m + 1) := by rw [← pow_succ]
    _ = _ := by ring

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m IH
  . simp
  calc
    _ = (x ^ n) ^ (m) * (x ^ n) := by rw [pow_succ]
    _ = (x ^ (n * m)) * (x ^ n) := by rw [IH]
    _ = (x ^ (n * m + n)) := by rw [pow_add]
    _ = _ := by ring

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n IH
  . simp
  calc
    _ = (x * y) ^ n * (x * y) := by rw [pow_succ]
    _ = (x ^ n * y ^ n) * (x * y) := by rw [IH]
    _ = (x ^ n * x) * (y ^ n * y) := by ring
    _ = _ := by rw [← pow_succ, ← pow_succ]

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor <;> intro h
  . contrapose! h
    rw [← Nat.exists_add_one_eq] at hn
    obtain ⟨ n, rfl ⟩ := hn
    induction' n with n IH
    . simp [h]
    rw [pow_succ]
    contrapose! IH
    simp at IH
    contradiction
  . simp [h]
    omega

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n IH
  . simp
  rw [pow_succ]
  exact Left.mul_nonneg IH hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n IH
  . simp
  rw [pow_succ]
  exact Left.mul_pos IH hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n IH
  . simp
  simp only [pow_succ]
  have hx : x ≥ 0 := by linarith
  gcongr

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  rw [gt_iff_lt, ← Nat.exists_add_one_eq] at hn
  obtain ⟨ n, rfl ⟩ := hn
  induction' n with n IH
  . simp [hxy]
  rw [pow_succ, pow_succ y _]
  gcongr

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n IH
  . simp
  rw [pow_succ, pow_succ, IH, abs_mul]

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from `DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain ⟨ m, hm ⟩ := Int.eq_nat_or_neg m
  obtain rfl | rfl := hn <;> obtain rfl | rfl := hm
  . norm_cast
    exact pow_add x m n
  . induction' m with m IH
    . simp
    rw [zpow_neg, pow_succ]
    have : (1 / (x ^ m * x)) = (1 / (x ^ m) * x⁻¹) := by ring
    rw [this, ← zpow_neg, ← mul_assoc, IH, ← zpow_sub_one₀]
    . have : ((n:ℤ) + -↑m - 1) = (↑n + -↑(m + 1)) := by omega
      rw [this]
    exact hx
  . induction' n with n IH
    . simp
    rw [zpow_neg, pow_succ]
    have : 1 / (x ^ n * x) * x ^ (m:ℤ) = 1 / (x ^ n) * x ^ (m:ℤ) * x⁻¹ := by ring
    rw [this, ← zpow_neg, IH, ← zpow_sub_one₀]
    . have : (-n + (m:ℤ) - 1) = (-↑(n + 1) + ↑m) := by omega
      rw [this]
    exact hx
  . rw [zpow_neg, zpow_neg]
    have : -(n:ℤ) + -↑m = -((n + m):ℕ) := by omega
    rw [this, zpow_neg, ← pow_add]
    ring

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain ⟨ m, hm ⟩ := Int.eq_nat_or_neg m
  obtain rfl | rfl := hn <;> obtain rfl | rfl := hm
  . exact pow_mul _ _ _
  . have : (↑n * -(m:ℤ)) = -((n * m):ℕ)
    . simp
    rw [zpow_neg, pow_eq_pow, this, zpow_neg, pow_mul]
  . have : (-n * (m:ℤ)) = -((n * m):ℕ) := by simp
    rw [zpow_neg, pow_eq_pow, this, zpow_neg]
    ring
  . have : (-n * -(m:ℤ)) = ((n * m):ℕ) := by simp
    rw [zpow_neg, zpow_neg, this, pow_eq_pow]
    simp
    rw [pow_mul]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain rfl | rfl := hn
  . norm_cast
    rw [mul_pow]
  . rw [zpow_neg, zpow_neg, zpow_neg]
    ring

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain rfl | rfl := hn
  . norm_cast
    exact pow_pos _ hx
  . rw [zpow_neg]
    have := pow_pos n hx
    exact one_div_pos.mpr this

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain rfl | rfl := hn
  . norm_cast
    apply pow_ge_pow
    . exact hxy
    . linarith
  . omega

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain rfl | rfl := hn
  . omega
  . rw [zpow_neg, zpow_neg, le_div_iff₀, mul_comm, ← le_div_iff₀]
    . simp
      apply pow_ge_pow
      . exact hxy
      linarith
    . simp
      have hx : x > 0 := by linarith
      exact pow_pos n hx
    . exact pow_pos n hy

theorem Real.pow_inj_helper {x y:Real} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  replace hn : 0 < n := by omega
  obtain h | h | h := lt_trichotomy x y
  . have : x ^ n < y ^ n
    . apply pow_gt_pow
      . exact h
      . linarith
      . exact hn
    linarith
  . exact h
  . have : x ^ n > y ^ n
    . apply pow_gt_pow
      . exact h
      . linarith
      exact hn
    linarith

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain rfl | rfl := hn
  . norm_cast at hxy hn
    exact pow_inj_helper hx hy hn hxy
  . rw [zpow_neg, zpow_neg] at hxy
    simp at hxy
    simp at hn
    exact pow_inj_helper hx hy hn hxy

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by
  obtain ⟨ n, hn ⟩ := Int.eq_nat_or_neg n
  obtain rfl | rfl := hn
  . exact pow_abs _ _
  . rw [zpow_neg, zpow_neg]
    have h := pow_abs x n
    rw [h]
    simp only [one_div, abs_inv]

/-- Definition 5.6.2.  We permit ``junk values'' when `x` is negative or `n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  simp
  rw [ge_iff_le, le_iff_exists_add] at hn
  obtain ⟨ n, rfl ⟩ := hn
  simp [hx]

theorem one_pow_gt_helper {y:Real} (n:ℕ) (hn: n ≥ 1) (hy : 1 < y) : 1 < y ^ n := by
  rw [ge_iff_le, le_iff_exists_add] at hn
  obtain ⟨ n, rfl ⟩ := hn
  induction' n with n IH
  . simp [hy]
  have : y ^ (1 + (n + 1)) = y ^ (1 + (n)) * y := by ring
  rw [this]; clear this
  calc
    _ < y ^ (1 + n) := IH
    _ = y ^ (1 + n) * 1 := by ring
    _ ≤ _ := by gcongr

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n
    . exact one_pow_gt_helper n hn hy'
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n
  . clear hy
    rw [ge_iff_le, le_iff_exists_add] at hn
    obtain ⟨ n, rfl ⟩ := hn
    induction' n with n IH
    . simp [hy']
    have : y ^ (1 + (n + 1)) = y ^ (1 + (n)) * y := by ring
    rw [this]; clear this
    calc
        _ < y ^ (1 + n) := IH
        _ = y ^ (1 + n) * 1 := by ring
        _ ≤ _ := by {
          have : 1 ≤ y := by linarith
          gcongr
        }
  linarith

theorem root_LUB_helper {n:ℕ} {x: Real} (hx: x ≥ 0) (hn: n ≥ 1) : IsLUB {y | 0 ≤ y ∧ y ^ n ≤ x} (x.root n) := by
  simp [Real.root]
  apply ExtendedReal.sSup_of_bounded
  . exact Real.rootset_nonempty hx n hn
  . exact Real.rootset_bddAbove n hn

theorem exists_less_pow_helper {x:Real} {n:ℕ} (hn: n ≥ 1) (hy: x > 0) : ∃ e:Real, e > 0 ∧ e ^ n < x := by
  rw [ge_iff_le, le_iff_exists_add] at hn
  obtain ⟨ n, rfl ⟩ := hn
  obtain h | h := lt_or_ge x 1
  . use (x/2), (by linarith)
    induction' n with n IH
    . simp [hy]
    have : (x / 2) ^ (1 + (n + 1)) = (x / 2) ^ (1 + n) * (x/2) := by ring
    rw [this]; clear this
    have hx2 : x/2 < 1 := by linarith
    set a := (x / 2) ^ (1 + n)
    have ha : a > 0
    . unfold a
      apply Real.pow_pos
      linarith
    have : a * (x / 2) < a * 1 := by gcongr
    linarith
  . use (1/2), (by norm_num)
    induction' n with n IH
    . simp
      linarith
    have : ((1:Real) / 2) ^ (1 + (n + 1)) = (1 / 2) ^ (1 + n) / 2 := by ring
    linarith

theorem add_eps_pow_helper {x y:Real} (n:ℕ) (hy: y > 0) (h: y ^ n < x) : ∃ e:Real, e > 0 ∧ e < y ∧ (y + e) ^ n < x := by
  induction' n with n IH generalizing x
  . simp at h
    use (y/2), (by linarith), (by linarith)
    simp [h]
  simp [pow_succ] at h
  replace h : y ^ n < x/y
  . exact (lt_div_iff₀ hy).mpr h
  specialize IH h
  obtain ⟨ e, he1, he2, he3 ⟩ := IH
  replace he3 : (y + e) ^ n * y < x := by exact (lt_div_iff₀ hy).mp he3
  rw [lt_iff_exists_pos_add] at he3
  obtain ⟨ c, hc1, hc2 ⟩ := he3
  rw [← hc2]
  have h2yg0 : (2 * y) ^ n > 0
  . apply Real.pow_pos
    linarith
  have he' : ∃ e' > 0, e' ≤ e ∧ e' < c / ((2 * y) ^ n)
  . use min e ((c / (2 * y) ^ n) / 2)
    simp
    split_ands
    . exact he1
    . exact div_pos hc1 h2yg0
    . right
      exact div_pos hc1 h2yg0
  obtain ⟨ e', he'1, he'2, he'3 ⟩ := he'
  use e', he'1, (by linarith)
  rw [pow_succ, mul_add]
  have hye'0 : (y + e') ≥ 0 := by linarith
  -- (y + e') ^ (n + 1) = (y + e') ^ n * y + (y + e') ^ n * e'
  -- < (y + e) ^ n * y + (2y) ^ n * e'
  -- <= (y + e) ^ n * y + c
  have g1 : (y + e') ^ n * y ≤ (y + e) ^ n * y
  . have : (y + e') ^ n ≤ (y + e) ^ n
    . have h2 : (y + e') ≤ (y + e) := by linarith
      exact Real.pow_ge_pow _ _ n h2 hye'0
    gcongr
  have g2 : (y + e') ^ n * e' < c
  . have : (y + e') ^ n * e' ≤ (2 * y) ^ n * e'
    . have : (y + e') ^ n ≤ (2 * y) ^ n
      . have h1 : (y + e') ≤ (2 * y) := by linarith
        exact Real.pow_ge_pow _ _ n h1 hye'0
      gcongr
    have : (2 * y) ^ n * e' < c
    . have h2yn0 : (2 * y) ^ n ≠ 0 := by linarith
      have : (2 * y) ^ n * e' < (2 * y) ^ n * (c / ((2 * y) ^ n))
      . gcongr
      have : (2 * y) ^ n * (c / (2 * y) ^ n) = c * ((2 * y) ^ n / (2 * y) ^ n) := by ring
      simp [h2yn0] at this
      linarith
    linarith
  linarith

theorem sub_eps_pow_helper {x y:Real} (n:ℕ) (hy: y > 0) (h: y ^ n > x) : ∃ e:Real, e > 0 ∧ e < y ∧ (y - e) ^ n > x := by
  induction' n with n IH generalizing x
  . simp at h
    use (y/2), (by linarith), (by linarith)
    simp [h]
  simp only [pow_succ] at h
  replace h : y ^ n > x/y
  . exact (div_lt_iff₀ hy).mpr h
  specialize IH h
  obtain ⟨ e, he1, he2, he3 ⟩ := IH
  replace he3 : (y - e) ^ n * y > x := by exact (div_lt_iff₀ hy).mp he3
  rw [gt_iff_lt, lt_iff_exists_pos_add] at he3
  obtain ⟨ c, hc1, hc2 ⟩ := he3
  replace hc2 : x = (y - e) ^ n * y - c := by linarith
  rw [hc2]
  have h2yg0 : y ^ n > 0
  . apply Real.pow_pos
    exact hy
  have he' : ∃ e' > 0, e' ≤ e ∧ e' < c / ((y) ^ n)
  . use min e ((c / (y) ^ n) / 2)
    simp
    split_ands
    . exact he1
    . exact div_pos hc1 h2yg0
    . right
      exact div_pos hc1 h2yg0
  obtain ⟨ e', he'1, he'2, he'3 ⟩ := he'
  use e', he'1, (by linarith)
  rw [pow_succ, mul_sub]
  have hye0 : (y - e) ≥ 0 := by linarith
  have hye'0 : (y - e') ≥ 0 := by linarith
  -- (y + e') ^ (n + 1) = (y + e') ^ n * y + (y + e') ^ n * e'
  -- < (y + e) ^ n * y + (2y) ^ n * e'
  -- <= (y + e) ^ n * y + c
  have g1 : (y - e') ^ n * y ≥ (y - e) ^ n * y
  . have : (y - e') ^ n ≥ (y - e) ^ n
    . have h2 : (y - e') ≥ (y - e) := by linarith
      exact Real.pow_ge_pow _ _ n h2 hye0
    gcongr
  have g2 : (y - e') ^ n * e' < c
  . have : (y - e') ^ n * e' ≤ (y) ^ n * e'
    . have : (y - e') ^ n ≤ (y) ^ n
      . have h1 : (y - e') ≤ (y) := by linarith
        exact Real.pow_ge_pow _ _ n h1 hye'0
      gcongr
    have : y ^ n * e' < c
    . have h2yn0 : (y) ^ n ≠ 0 := by linarith
      have : (y) ^ n * e' < (y) ^ n * (c / ((y) ^ n))
      . gcongr
      have : (y) ^ n * (c / (y) ^ n) = c * ((y) ^ n / (y) ^ n) := by ring
      simp [h2yn0] at this
      linarith
    linarith
  linarith

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
  have hlb := root_LUB_helper hx hn
  rw [isLUB_def] at hlb
  obtain ⟨ h1, h2 ⟩ := hlb
  constructor <;> intro h
  . rw [← h] at h1 h2
    clear h
    by_contra hy2
    obtain h | h | h := lt_trichotomy (y ^ n) x
    . -- If y ^ n < x, then we've broken the upper bound assertion.
      -- There must exist some small positive e such that (y + e) ^ n < x.
      -- Prove this with induction.
      contrapose! h1
      rw [upperBound_def]
      push_neg
      -- y = 0 is some degenerate case...
      rw [ge_iff_le, le_iff_eq_or_lt] at hy
      obtain hy | hy := hy
      . have : n ≠ 0 := by omega
        simp [← hy, this] at h
        obtain ⟨ e, he1, he2 ⟩ := exists_less_pow_helper hn h
        use e
        simp
        split_ands
        . linarith
        . linarith
        . simp [← hy, he1]
      obtain ⟨ e, he1, _, he2 ⟩ := add_eps_pow_helper n hy h
      use (y+e)
      simp
      split_ands
      . linarith
      . linarith
      . exact he1
    . contradiction
    . -- If y ^ n > x, then we need to show it's not the least upper bound...
      contrapose! h2; clear h2
      rw [ge_iff_le, le_iff_eq_or_lt] at hy
      obtain hy | hy := hy
      . have : n ≠ 0 := by omega
        simp [← hy, this] at h
        linarith
      obtain ⟨ e, he1, he2, he3 ⟩ := sub_eps_pow_helper n hy h
      use (y-e)
      constructor
      . rw [upperBound_def]
        intro y' hy'
        simp at hy'
        obtain ⟨ hy'1, hy'2 ⟩ := hy'
        contrapose! he3
        have : (y - e) ^ n < y' ^ n
        . apply Real.pow_gt_pow
          . exact he3
          . linarith
          . omega
        linarith
      . linarith
  . -- Need to prove least upper bound of {y'|y' ^ n <= x} = y.
    -- We know y ^ n = x.
    -- If y > y', then we've broken the upper bound assertion.
    -- If y < y', then we've broken the least part of the assertion.
    set y' := x.root n
    by_contra hy'
    obtain h3 | h3 | h3 := lt_trichotomy y y'
    . contrapose! h2
      use y
      constructor
      . rw [upperBound_def]
        intro z hz
        simp at hz
        replace hz := hz.2
        rw [← h] at hz
        contrapose! hz
        exact pow_gt_pow z y n hz hy hn
      . exact h3
    . contradiction
    . contrapose! h1
      rw [upperBound_def]
      push_neg
      use y
      simp [hy, h3]
      linarith

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  -- LUB should be >= 0. If it was less, then consider 0 in set.
  have h := root_LUB_helper hx hn
  rw [isLUB_def] at h
  replace h := h.1
  contrapose! h
  rw [upperBound_def]
  push_neg
  use 0
  simp
  constructor
  . replace hn : n ≠ 0 := by omega
    simp [hn, hx]
  . exact h

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  have h : x.root n = x.root n := by rfl
  rw [Real.eq_root_iff_pow_eq] at h
  . exact h
  . exact hx
  . apply Real.root_nonneg
    . exact hx
    . exact hn
  . exact hn

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  constructor <;> intro h
  . have hpow : (x.root n)^n > 0 := by exact pow_pos n h
    have he := pow_of_root hx hn
    linarith
  . contrapose! h
    have := root_nonneg hx hn
    replace h : x.root n = 0 := by linarith
    clear this
    have hpow : (x.root n)^n = 0
    . simp [h]
      omega
    have he := pow_of_root hx hn
    linarith

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  symm
  rw [Real.eq_root_iff_pow_eq]
  . exact pow_nonneg n hx
  . exact hx
  . exact hn

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  have hex := pow_of_root hx hn
  have hey := pow_of_root hy hn
  constructor <;> intro h
  . rw [← hex, ← hey] at h
    contrapose! h
    have hx0 := root_nonneg hx hn
    exact pow_ge_pow _ _ n h hx0
  . rw [← hex, ← hey]
    have hy0 := root_nonneg hy hn
    exact pow_gt_pow _ _ n h hy0 hn

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  symm
  rw [Real.eq_root_iff_pow_eq]
  . exact one_pow k
  . norm_num
  . norm_num
  . exact hk

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  set j := l
  -- Assume to the contrary that x.root j <= x.root k
  -- Then (x.root j)^j <= (x.root k)^j.
  -- But that means x = (x.root k)^k <= (x.root k)^j which is impossible.
  -- Depends on x.root k > 1...
  by_contra h
  simp at h
  have hx2 : x ≥ 0 := by linarith
  have hj0 := root_nonneg hx2 hl
  have hpow : (x.root j)^j ≤ (x.root k)^j := by exact pow_ge_pow _ _ j h hj0
  have hje := pow_of_root hx2 hl
  have hk : k ≥ 1 := by linarith
  have hke := pow_of_root hx2 hk
  have : x.root k ^ k > x.root k ^ j
  . set x' := x.root k
    have hx' : x' > 1
    . unfold x'
      have := (root_mono hx2 (by norm_num) hk).mp hx
      have := root_of_one hk
      linarith
    rw [gt_iff_lt, lt_iff_exists_pos_add] at hkl
    obtain ⟨ c, hc, rfl ⟩ := hkl
    rw [← pow_add]
    have : x' ^ c > 1
    . exact one_pow_gt_helper c (by omega) hx'
    have : x' ^ j * x' ^ c > x' ^ j * 1
    . gcongr
    linarith
  linarith

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  set j := l
  by_contra h
  simp at h
  -- x <= (x.root j) ^ k
  -- (x.root j) ^ j <= (x.root j) ^ k
  -- (x.root j) ^ j <= (x.root j) ^ (j + c)
  -- Contradiction!
  have hx2 : x ≥ 0 := by linarith
  have hk : k ≥ 1 := by linarith
  have hj0 := root_nonneg hx2 hl
  have hk0 := root_nonneg hx2 hk
  have hpow : (x.root k)^k ≤ (x.root j)^k := by exact pow_ge_pow _ _ k h hk0
  have hje := pow_of_root hx2 hl
  have hke := pow_of_root hx2 hk
  have : x.root j ^ j > x.root j ^ k
  . rw [gt_iff_lt, lt_iff_exists_pos_add] at hkl
    obtain ⟨ c, hc, rfl ⟩ := hkl
    rw [← pow_add]
    have : x.root j ^ j * 1 > x.root j ^ j * x.root j ^ c
    . have h1 : x.root j > 0
      . rw [root_pos]
        . exact hx0
        . exact hx2
        . exact hl
      have h2 : x.root j < 1
      . have := root_of_one hl
        rw [← this]; clear this
        rw [← gt_iff_lt, ← root_mono]
        . exact hx
        . norm_num
        . exact hx2
        . exact hl
      gcongr
      have : (1:Real) = 1 ^ c := by ring
      rw [this]; clear this
      exact pow_gt_pow _ _ c h2 hj0 hc
    linarith
  linarith

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  symm
  rw [Real.eq_root_iff_pow_eq]
  . rw [mul_pow, pow_of_root hx hn, pow_of_root hy hn]
  . exact Left.mul_nonneg hx hy
  . have h1 := by exact root_nonneg hx hn
    have h2 := by exact root_nonneg hy hn
    exact Left.mul_nonneg h1 h2
  . exact hn

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  have h1 := by exact root_nonneg hx hn
  rw [Real.eq_root_iff_pow_eq]
  . have : (x.root n).root m ^ (n * m) = ((x.root n).root m ^ (m)) ^ n := by ring
    rw [this]; clear this
    rw [pow_of_root h1 hm, pow_of_root hx hn]
  . exact hx
  . exact root_nonneg h1 hm
  . exact Right.one_le_mul hn hm

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  symm
  have h1 : x ≥ 0 := by linarith
  rw [Real.eq_root_iff_pow_eq]
  . simp
  . exact h1
  . exact h1
  . norm_num

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  have h2 : (y^n).root n = (z^n).root n := by rw [h]
  rwa [root_of_pow (by linarith) hn, root_of_pow (by linarith) hn] at h2

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0
    . simp [ha] at hq
      have hb'0 : (b':ℚ) ≠ 0
      . norm_cast
        linarith
      have : (0:ℚ) * b' = a'
      . exact (eq_mul_inv_iff_mul_eq₀ hb'0).mp hq
      simp at this
      norm_cast at this
      exact this.symm
    simp_all
  have : a' > 0
  . norm_cast at hq
    rw [Rat.divInt_eq_divInt] at hq
    . have : a' * b > 0
      . suffices h : a * b' > 0
        . rwa [← hq]
        have hb'0 : b' > (0:ℤ) := by omega
        exact Int.mul_pos ha hb'0
      have hb0 : b > (0:ℤ) := by omega
      exact Int.pos_of_mul_pos_left this hb0
    . omega
    . omega
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, mul_comm, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  have h1 := ratPow_def (b:= n) hx 1 (by omega)
  have : (1:ℚ) = (1:ℤ) := by norm_num
  rw [this, h1]; clear this h1
  simp

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  have h1 := ratPow_def (b:= 1) hx n (by norm_num)
  have : (n:ℚ) = (n/(1:ℕ):ℚ) := by simp
  rw [this, h1]; clear this h1
  rw [root_one hx]

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  rw [ratPow_def]
  . have h1 : x.root b > 0
    . rw [← root_pos (n := b)] at hx
      . exact hx
      . linarith
      . omega
    exact zpow_pos a h1
  . exact hx
  . exact hb

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  obtain ⟨ c, d, hd, rfl ⟩ := Rat.eq_quot r
  have : (a:ℚ) / ↑b + ↑c / ↑d = ((a * d + c * b):ℤ) / ((b * d):ℕ)
  . field_simp
  have hbd := Nat.mul_pos hb hd
  have hx2 : x ≥ 0 := by linarith
  rw [this, ratPow_def, ratPow_def, ratPow_def]
  . have h1 : x.root b ^ a = x.root (b * d) ^ (a * ↑d)
    . rw [← root_root, mul_comm, ← zpow_mul]
      . norm_cast
        rw [pow_of_root]
        . apply root_nonneg
          . exact hx2
          omega
        omega
      . exact hx2
      . omega
      omega
    have h2 : x.root d ^ c = x.root (b * d) ^ (c * ↑b)
    . rw [mul_comm, mul_comm c _, ← root_root, ← zpow_mul]
      . norm_cast
        rw [pow_of_root]
        . apply root_nonneg
          . exact hx2
          omega
        omega
      . exact hx2
      . omega
      omega
    rw [h1, h2, zpow_add]
    have := (root_pos hx2 hbd).mpr hx
    linarith
  . exact hx
  . exact hd
  . exact hx
  . exact hb
  . exact hx
  . exact hbd

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  obtain ⟨ c, d, hd, rfl ⟩ := Rat.eq_quot r
  have hx2 : x ≥ 0 := by linarith
  have hbd : b * d > 0 := by exact Nat.mul_pos hb hd
  have hxrb0 : x.root b ≥ 0
  . apply root_nonneg
    . exact hx2
    omega
  have : ((a:ℚ) / ↑b * (↑c / ↑d)) = (((a * c):ℤ) / ((b * d):ℕ))
  . field_simp
  rw [ratPow_def, ratPow_def, this, ratPow_def, ← zpow_mul]
  . suffices h : (x.root b ^ a).root d = (x.root (b * d) ^ a)
    . rw [h]
    clear this c
    symm
    rw [eq_root_iff_pow_eq]
    . have : (x.root (b * d) ^ a) ^ d = (x.root (b * d) ^ d) ^ a
      . set x' := x.root (b * d)
        have h1 : (x' ^ d) ^ a = (x' ^ (d:ℤ)) ^ a := by norm_cast
        have h2 : (x' ^ a) ^ d = (x' ^ a) ^ (d:ℤ) := by norm_cast
        rw [h1, h2, zpow_mul, zpow_mul, mul_comm]
      rw [this]
      suffices h : (x.root (b * d) ^ d) = x.root b
      . rw [h]
      rw [← root_root, pow_of_root]
      . exact hxrb0
      . omega
      . exact hx2
      . omega
      omega
    . exact zpow_nonneg hxrb0 a
    . have : x.root (b * d) ≥ 0
      . apply root_nonneg
        . exact hx2
        omega
      exact zpow_nonneg this a
    omega
  . exact hx
  . exact hbd
  . exact hx
  . exact hb
  . apply ratPow_pos
    exact hx
  . exact hd

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  have : (-((a:ℚ) / ↑b)) = (((-a):ℤ) / ↑b)
  . simp
    ring
  rw [ratPow_def, this, ratPow_def]
  . simp
  . exact hx
  . exact hb
  . exact hx
  . exact hb

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  have ha : a > 0
  . have ha : (a:ℚ) > 0
    . have hb : (b:ℚ) > 0
      . norm_cast
      exact (div_pos_iff_of_pos_right hb).mp h
    norm_cast at ha
  constructor <;> intro h1
  . rw [ratPow_def, ratPow_def]
    . have ha2 : a ≥ 0 := by omega
      lift a to ℕ using ha2
      norm_cast at ha
      norm_cast
      apply pow_gt_pow
      . rw [← root_mono]
        . exact h1
        . linarith
        . linarith
        omega
      . apply root_nonneg
        . linarith
        omega
      . exact ha
    . exact hy
    . exact hb
    . exact hx
    exact hb
  . have hx2 : x ≥ 0 := by linarith
    have hy2 : y ≥ 0 := by linarith
    rw [ratPow_def, ratPow_def] at h1
    . contrapose! h1
      apply zpow_ge_zpow
      . contrapose! h1
        rw [← gt_iff_lt, ← root_mono] at h1
        . exact h1
        . exact hx2
        . exact hy2
        omega
      . exact (root_pos hx2 hb).mpr hx
      exact ha
    . exact hy
    . exact hb
    . exact hx
    . exact hb

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  obtain ⟨ c, d, hd, rfl ⟩ := Rat.eq_quot r
  have hx2 : x > 0 := by linarith
  have hx3 : x ≥ 0 := by linarith
  have hbd : b * d ≥ 1 := by exact Right.one_le_mul hb hd
  rw [ratPow_def, ratPow_def]
  . have h1 : x.root b ^ a = x.root (b*d) ^ (a*d)
    . rw [mul_comm a d, ← zpow_mul]
      suffices h : x.root b = (x.root (b * d) ^ ↑d)
      . simp [h]
      rw [← root_root]
      . symm
        apply pow_of_root
        . exact root_nonneg hx3 (by omega)
        omega
      . exact hx3
      . omega
      exact hd
    have h2 : x.root d ^ c = x.root (b*d) ^ (c*b)
    . have : x.root (b * d) ^ (c * ↑b) = (x.root (b * d) ^ b) ^ c
      . rw [mul_comm c b, ← zpow_mul]
        simp
      rw [this]
      suffices h : x.root d = (x.root (b * d) ^ b)
      . rw [h]
      symm
      rw [eq_root_iff_pow_eq]
      . rw [pow_mul]
        apply pow_of_root
        . exact hx3
        exact hbd
      . exact hx3
      . have : x.root (b * d) ≥ 0 := by exact root_nonneg hx3 hbd
        exact pow_nonneg b this
      omega
    rw [h1, h2]
    set x' := x.root (b*d)
    have hx' : x' > 1
    . unfold x'
      have : 1 = (1:Real).root (b*d)
      . symm
        apply root_of_one
        exact hbd
      rw [this, ← root_mono]
      . exact hx
      . exact hx3
      . norm_num
      . exact hbd
    norm_cast
    constructor <;> intro h
    . contrapose! h
      rw [Rat.divInt_le_divInt] at h
      . exact (zpow_le_zpow_iff_right₀ hx').mpr h
      . omega
      . omega
    . contrapose! h
      rw [Rat.divInt_le_divInt]
      . rwa [← zpow_le_zpow_iff_right₀ hx']
      . omega
      . omega
  . exact hx2
  . exact hd
  . exact hx2
  . exact hb

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  obtain ⟨ c, d, hd, rfl ⟩ := Rat.eq_quot r
  have hx2 : x > 0 := by linarith
  have hx3 : x ≥ 0 := by linarith
  have hbd : b * d ≥ 1 := by exact Right.one_le_mul hb hd
  rw [ratPow_def, ratPow_def]
  . have h1 : x.root b ^ a = x.root (b*d) ^ (a*d)
    . rw [mul_comm a d, ← zpow_mul]
      suffices h : x.root b = (x.root (b * d) ^ ↑d)
      . simp [h]
      rw [← root_root]
      . symm
        apply pow_of_root
        . exact root_nonneg hx3 (by omega)
        omega
      . exact hx3
      . omega
      exact hd
    have h2 : x.root d ^ c = x.root (b*d) ^ (c*b)
    . have : x.root (b * d) ^ (c * ↑b) = (x.root (b * d) ^ b) ^ c
      . rw [mul_comm c b, ← zpow_mul]
        simp
      rw [this]
      suffices h : x.root d = (x.root (b * d) ^ b)
      . rw [h]
      symm
      rw [eq_root_iff_pow_eq]
      . rw [pow_mul]
        apply pow_of_root
        . exact hx3
        exact hbd
      . exact hx3
      . have : x.root (b * d) ≥ 0 := by exact root_nonneg hx3 hbd
        exact pow_nonneg b this
      omega
    rw [h1, h2]
    set x' := x.root (b*d)
    have hx' : x' < 1
    . unfold x'
      have : 1 = (1:Real).root (b*d)
      . symm
        apply root_of_one
        exact hbd
      rw [this, ← gt_iff_lt, ← root_mono]
      . exact hx
      . norm_num
      . exact hx3
      . exact hbd
    have hx'2 : x' > 0
    . unfold x'
      rw [root_pos]
      . exact hx0
      . exact hx3
      exact hbd
    norm_cast
    constructor <;> intro h
    . contrapose! h
      rw [Rat.divInt_le_divInt] at h
      . exact (zpow_le_zpow_iff_right_of_lt_one₀ hx'2 hx').mpr h
      . omega
      . omega
    . contrapose! h
      rw [Rat.divInt_le_divInt]
      . rwa [← zpow_le_zpow_iff_right_of_lt_one₀ hx'2 hx']
      . omega
      . omega
  . exact hx2
  . exact hd
  . exact hx2
  . exact hb

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  obtain ⟨ a, b, hb, rfl ⟩ := Rat.eq_quot q
  have hx2 : x ≥ 0 := by linarith
  have hy2 : y ≥ 0 := by linarith
  rw [ratPow_def, ratPow_def, ratPow_def, ← mul_zpow, root_mul]
  . exact hx2
  . exact hy2
  . omega
  . exact hy
  . exact hb
  . exact hx
  . exact hb
  . exact Left.mul_pos hx hy
  . exact hb

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  -- Induction, need to assert property for odd.
  have (n':ℕ) (hx: x < 0) : (Even n' ∧ x^n' ≥ 0) ∨ (Odd n' ∧ (x^n' ≤ 0))
  . clear hn n
    have hx2 : x ≤ 0 := by linarith
    induction' n' with n' IH
    . left
      constructor <;> simp
    obtain ⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩ := IH
    . right
      constructor
      . exact Even.add_one h1
      rw [pow_succ]
      exact mul_nonpos_of_nonneg_of_nonpos h2 hx2
    . left
      constructor
      . exact Odd.add_one h1
      rw [pow_succ]
      exact mul_nonneg_of_nonpos_of_nonpos h2 hx2
  obtain hx | hx := lt_or_ge x 0
  . specialize this n hx
    obtain h | h := this
    . exact h.2
    have : ¬ Odd n := by exact Nat.not_odd_iff_even.mpr hn
    tauto
  . exact pow_nonneg n hx

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  wlog h : x ≥ y generalizing x y
  . specialize this hy hx (by linarith)
    rw [max_comm, this, max_comm]
  simp [h]
  contrapose! h
  rw [← gt_iff_lt, ← ratPow_mono] at h
  . exact h
  . exact hy
  . exact hx
  . exact hq

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  wlog h : x ≥ y generalizing x y
  . specialize this hy hx (by linarith)
    rw [min_comm, this, min_comm]
  simp [h]
  contrapose! h
  rw [← gt_iff_lt, ← ratPow_mono] at h
  . exact h
  . exact hy
  . exact hx
  . exact hq

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
