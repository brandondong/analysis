import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/

abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    unfold Real.Close
    simp_rw [Real.dist_eq]
    constructor <;> intro h e he N hN <;> specialize h e he N hN <;>
      obtain ⟨ n, hn, h ⟩ := h <;> use n
    . simp [hn] at h
      simp at hn
      use hn.2
    . have hn2 : n ≥ max a.m N := by omega
      simp [hn2, h]

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  use 0
  simp [Real.dist_eq]
  norm_num

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by
  unfold Real.ContinuallyAdherent
  push_neg
  use 1
  simp
  intro n hn
  have hn2 : 0 ≤ n := by omega
  simp [hn, Real.dist_eq, hn2]
  have h10 : (10:ℝ)  ^ (-n - 1) < 0.1 := by sorry
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  intro n hn
  use n
  simp [hn]
  sorry

/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by sorry

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by sorry

/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by sorry

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by sorry

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by sorry

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by sorry

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  intro e he N hN
  unfold Real.Adherent
  specialize h e he
  obtain ⟨ N', hN', h ⟩ := h
  rw [Real.closeSeq_def] at h
  use max N N'
  constructor
  . simp [hN]
  rw [Real.Close, Real.dist_eq]
  simp [hN]
  specialize h (max N N') (by simp [hN'])
  simp [Real.dist_eq, hN'] at h
  exact h

theorem Sequence.limit_point_of_limit_unique {a:Sequence} {x y:ℝ} (h: a.TendsTo x) (hy: a.LimitPoint y) : x = y := by
  have hx := limit_point_of_limit h
  have ha : a.IsCauchy
  . rw [Sequence.lim_eq] at h
    exact Sequence.IsCauchy.convergent h.1
  contrapose! ha; clear h
  wlog h : x < y
  . simp at h
    exact this hx hy (by symm; exact ha) (by contrapose! ha; linarith)
  clear ha
  rw [lt_iff_exists_pos_add] at h
  obtain ⟨ c, hc, rfl ⟩ := h
  rw [Sequence.isCauchy_def]
  push_neg
  use (c/4), (by linarith)
  intro N hN
  rw [Real.steady_def]
  push_neg
  specialize hx (c/4) (by linarith) N hN
  specialize hy (c/4) (by linarith) N hN
  obtain ⟨ n, hn, hx ⟩ := hx
  obtain ⟨ m, hm, hy ⟩ := hy
  use n, hn, m, hm
  rw [Real.Close, Real.dist_eq] at *
  set b := (a.from N).seq n
  set d := (a.from N).seq m
  by_contra h
  simp at h
  rw [abs_le] at *
  linarith

/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

example (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
  sorry

example : Example_6_4_7.limsup = 1 := by sorry

example (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

example : Example_6_4_7.liminf = -1 := by sorry

example : Example_6_4_7.sup = (1.1:ℝ) := by sorry

example : Example_6_4_7.inf = (-1.01:ℝ) := by sorry

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

theorem Example_6_4_8_upperseq (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by
  simp [Sequence.upperseq, Sequence.sup]
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . intro a _
    simp [le_iff]
  . intro b hb'
    obtain hb | rfl | rfl := EReal.def b
    . obtain ⟨ b, rfl ⟩ := hb; clear hb'
      obtain ⟨ m, hm ⟩ := exists_nat_gt b
      set n' := max n m
      use ((if Even n' then n'+1 else n'+2):ℝ)
      simp
      constructor
      . use (if Even n' then n' else n'+1)
        have hn : ((n:ℤ) ≤ if Even n' then ↑n' else n' + (1:ℤ))
        . suffices h : n ≤ n'
          . omega
          simp [n']
        have h0 : ((0:ℤ) ≤ if Even n' then ↑n' else n' + (1:ℤ))
        . have h : 0 ≤ n' := by simp
          by_cases hn' : Even n' <;> simp [hn']
          . linarith
        simp [hn, h0]
        by_cases h : Even n' <;> simp [h]
        . have h2 : Even (n' + 1)
          . simp at h
            exact Odd.add_one h
          simp [h2]
          ring
      . suffices h : b < n'
        . by_cases hn' : Even n' <;> simp [hn'] <;> linarith
        simp [n', hm]
    . simp at hb'
    . use ((if Even n then (n:ℝ) + (1:ℝ) else -n - 1):ℝ)
      constructor
      . simp
        use n
        simp
      simp

example : Example_6_4_8.limsup = ⊤ := by
  simp [Sequence.limsup]
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . intro a ha
    simp at ha
    obtain ⟨ N, hN, rfl ⟩ := ha
    lift N to ℕ using hN
    simp [Example_6_4_8_upperseq]
  . intro b hb
    use ⊤
    simp [hb]
    use 0, (by norm_num)
    have h0 : (0:ℤ) = (0:ℕ) := by ring
    rw [h0]
    simp only [Example_6_4_8_upperseq]

example (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by sorry

example : Example_6_4_8.liminf = ⊥ := by sorry

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹ := by sorry

example : Example_6_4_9.limsup = 0 := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by sorry

example : Example_6_4_9.liminf = 0 := by sorry

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

example (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by sorry

example : Example_6_4_10.limsup = ⊤ := by sorry

theorem Example_6_4_10_lowerseq (n:ℕ) : Example_6_4_10.lowerseq n = n+1 := by
  simp [Sequence.lowerseq, Sequence.inf]
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  . intro a ha
    simp at ha
    obtain ⟨ n', hn', rfl ⟩ := ha
    simp [hn']
    have h0 : 0 ≤ n' := by omega
    simp [h0]
    norm_cast
    omega
  . intro b hb
    use n+1
    simp [hb]
    use n
    simp

example : Example_6_4_10.liminf = ⊤ := by
  simp [Sequence.liminf]
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  . intro a ha
    simp [le_iff]
  . intro b hb2
    obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
    . obtain ⟨ n, hn ⟩ := exists_nat_gt y
      use n+1
      simp
      constructor
      . use n
        constructor
        . norm_cast
          simp
        simp [Example_6_4_10_lowerseq]
      norm_cast
      simp
      linarith
    . simp at hb2
    . use 1
      simp
      constructor
      . use 0
        simp
        have h0 : (0:ℤ) = (0:ℕ) := by ring
        rw [h0]
        simp only [Example_6_4_10_lowerseq]
        simp
      . tauto

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp only [limsup, sInf_lt_iff] at h
  obtain ⟨y, hy, ha⟩ := h
  obtain ⟨N, hN, hNy⟩ := hy
  rw [hNy] at ha; use N
  simp [hN, upperseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

theorem Sequence.lt_sInf_iff_helper {y:EReal} {S: Set EReal} (h: y < sInf S) : ∀ x ∈ S, y < x := by
  intro s hs
  have hy : sInf S = sInf S := by rfl
  rw [← isGLB_iff_sInf_eq, isGLB_iff_le_iff] at hy
  replace hy := (hy (sInf S)).mp (by simp)
  simp [lowerBounds] at hy
  specialize hy hs
  exact Std.lt_of_lt_of_le h hy

theorem Sequence.sSup_lt_iff_helper {y:EReal} {S: Set EReal} (h: sSup S < y) : ∀ x ∈ S, x < y := by
  intro x hx
  have hy : IsLUB S (sSup S) := by exact CompleteLattice.isLUB_sSup S
  set x' := sSup S
  rw [isLUB_iff_le_iff] at hy
  replace hy := (hy x').mp (by simp)
  simp [upperBounds] at hy
  specialize hy hx
  exact Std.lt_of_le_of_lt hy h

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  simp [liminf] at h
  rw [lt_sSup_iff] at h
  obtain ⟨ x, hx, hxy ⟩ := h
  simp at hx
  obtain ⟨ N, hN, rfl ⟩ := hx
  use N, hN
  simp [lowerseq, inf] at hxy
  have h := lt_sInf_iff_helper hxy
  intro n hn
  specialize h (a.seq n)
  apply h
  simp
  use n
  have hn2 : a.m ≤ n := by omega
  simp [hn2, hn]

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  simp [liminf] at h
  replace h := Sequence.sSup_lt_iff_helper h (a.lowerseq N) (by {
    simp
    use N
  })
  simp [lowerseq] at h
  obtain ⟨ n, hn, h, _ ⟩ := Sequence.exists_between_gt_inf h
  simp at hn
  use n, hn.2
  simp [hn] at h
  exact h

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  simp [liminf]
  rw [le_sSup_iff]
  intro b hb
  simp [upperBounds] at hb
  have h : a.inf = a.lowerseq a.m
  . simp [lowerseq]
    suffices h : a = (a.from a.m)
    . rw [← h]
    ext n
    . simp
    . simp
      exact a.vanish n
  exact hb a.m (by simp) h

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by
  simp only [liminf, limsup]
  rw [sSup_le_iff]
  intro b hb
  rw [le_sInf_iff]
  intro c hc
  simp at hb hc
  obtain ⟨ N, hN, rfl ⟩ := hb
  obtain ⟨ M, hM, rfl ⟩ := hc
  simp [lowerseq, inf]
  rw [sInf_le_iff]
  intro b hb
  simp [lowerBounds] at hb
  -- b <= a.seq n where n >= N.
  simp [upperseq, sup]
  rw [le_sSup_iff]
  intro c hc
  simp [upperBounds] at hc
  -- c >= a.seq n where n >= M.
  -- Use max N M.
  set P := max N M
  have hp : a.m ≤ P
  . simp [P, hN]
  have hmp : M ≤ P := by simp [P]
  have hnp : N ≤ P := by simp [P]
  replace hc := hc (a := a.seq P) P hp hmp
  simp [hp, hmp] at hc
  replace hb := hb (a := a.seq P) P hp hnp
  simp [hp, hnp] at hb
  exact EReal.trans hb hc

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by sorry

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  rw [Sequence.limit_point_def] at h
  -- a contains distant points that are arbitrarily close to c.
  constructor
  . simp [liminf]
    intro b n hn rfl
    simp [lowerseq, inf]
    rw [sInf_le_iff]
    intro b hb
    -- If c < b (lower bound), then c <= all a.seq n by some constant.
    simp [lowerBounds] at hb
    obtain ⟨ b, rfl ⟩ | rfl | rfl := EReal.def b
    . contrapose! h
      simp at h
      rw [lt_iff_exists_pos_add] at h
      obtain ⟨ e, he, rfl ⟩ := h
      use (e/2), (by linarith)
      use n, hn
      intro m hm
      have hm2 : a.m ≤ m := by omega
      replace hb := hb (a := a.seq m) m hm2 hm
      simp [hm2, hm] at hb
      norm_cast at hb
      set d := a.seq m
      rw [lt_abs]
      left
      linarith
    . have h1 := hb (a := a.seq n) n hn (by simp)
      simp [hn, le_iff] at h1
      tauto
    . simp
  sorry

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  sorry

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  rw [Sequence.limit_point_def]
  intro e he N hN
  -- We know upper(inf a.from N) > L_minus - e
  -- or there is some M where inf a.from M > L_minus - e
  -- or all a n where n >= M.
  have hge : a.liminf ≥ L_minus := by simp [h]
  simp [liminf] at hge
  replace hge : ((L_minus - e):ℝ) < sSup {x | ∃ N, a.m ≤ N ∧ x = a.lowerseq N}
  . set b := sSup {x | ∃ N, a.m ≤ N ∧ x = a.lowerseq N}
    have : ((L_minus-e):ℝ) < (L_minus:EReal)
    . norm_cast
      linarith
    exact lt_of_lt_of_eq this (h.symm)
  rw [lt_sSup_iff] at hge
  obtain ⟨ b, hb, hge ⟩ := hge
  simp at hb
  obtain ⟨ M, hM, rfl ⟩ := hb
  simp [lowerseq, inf] at hge
  replace hge := lt_sInf_iff_helper hge
  -- inf a.from N <= L_minus or < L_minus + e in which case there is some a n < L_minus + e.
  have hle : a.liminf ≤ L_minus := by simp [h]
  simp [liminf] at hle
  replace hle := hle (a.lowerseq (max M N)) (max M N) (by simp [hM]) (by rfl)
  simp [lowerseq] at hle
  replace hle : (a.from (max M N)).inf < ((L_minus + e):ℝ)
  . set b := (a.from (max M N)).inf
    have : (L_minus:EReal) < ((L_minus+e):ℝ)
    . norm_cast
      linarith
    exact Std.lt_of_le_of_lt hle this
  obtain ⟨ n, hn, hlt, _ ⟩ := exists_between_gt_inf hle
  simp at hn
  simp [hn] at hlt
  norm_cast at hlt
  specialize hge (a.seq n) (by simp; use n; simp [hn])
  norm_cast at hge
  use n
  simp [hn]
  rw [abs_le]
  set b := a.seq n
  constructor <;> linarith

theorem Sequence.lowerseq_neq_top (a:Sequence) (N:ℤ) (hN : a.m ≤ N) : ¬ a.lowerseq N = ⊤ := by
  intro h
  simp [lowerseq, inf] at h
  rw [← isGLB_iff_sInf_eq, isGLB_iff_le_iff] at h
  replace h := (h ⊤).mp (by simp)
  simp [lowerBounds] at h
  contrapose! h
  use (a.seq N), N
  simp [hN]

theorem Sequence.tendsTo_if_eq_limsup_liminf_helper {a:Sequence} (c:ℝ) (h: a.liminf = c ∧ a.limsup = c) :
  a.TendsTo c := by
  rw [Sequence.tendsTo_def]
  obtain ⟨ hi, hs ⟩ := h
  intro e he
  rw [Real.eventuallyClose_def]
  -- sSup (a.from N inf) = c or > c-e -> a.from N > c-e.
  -- sInf (a.from N sup) = c or < c+e -> a.from N < c+e.
  replace hi : a.liminf > ((c-e):ℝ)
  . rw [hi]
    norm_cast
    linarith
  replace hs : a.limsup < ((c+e):ℝ)
  . rw [hs]
    norm_cast
    linarith
  simp [liminf] at hi
  simp [limsup] at hs
  rw [lt_sSup_iff] at hi
  obtain ⟨ b, hb, hi ⟩ := hi
  simp at hb
  obtain ⟨ N, hN, rfl ⟩ := hb
  rw [sInf_lt_iff] at hs
  obtain ⟨ b, hb, hs ⟩ := hs
  simp at hb
  obtain ⟨ M, hM, rfl ⟩ := hb
  simp [lowerseq, inf] at hi
  simp [upperseq, sup] at hs
  replace hi := le_of_lt hi
  replace hs := le_of_lt hs
  rw [le_sInf_iff] at hi
  rw [sSup_le_iff] at hs
  use max N M, (by simp [hN])
  rw [Real.closeSeq_def]
  intro n hn
  simp at hn
  simp [Real.dist_eq, hn]
  specialize hi (a.seq n) (by simp; use n; simp [hn])
  specialize hs (a.seq n) (by simp; use n; simp [hn])
  norm_cast at hi hs
  rw [abs_le]
  constructor <;> linarith

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  constructor <;> intro h
  . constructor
    . simp [liminf]
      apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
      . intro b hb
        simp at hb
        obtain ⟨ N, hN, rfl ⟩ := hb
        contrapose! h
        obtain ⟨ b, hb ⟩ | h1 | h1 := EReal.def (a.lowerseq N)
        . rw [← hb] at h
          simp at h
          rw [lt_iff_exists_pos_add] at h
          obtain ⟨ d, hd, rfl ⟩ := h
          simp [lowerseq, inf] at hb
          symm at hb
          rw [← isGLB_iff_sInf_eq, isGLB_iff_le_iff] at hb
          replace hb := (hb (c+d)).mp (by simp)
          simp [lowerBounds] at hb
          rw [Sequence.tendsTo_def]
          push_neg
          use (d/2), (by linarith)
          intro M hM
          rw [Real.closeSeq_def]
          push_neg
          replace hb := hb (a := a.seq (max M N)) (max M N) (by simp [hM]) (by simp)
          simp [hM] at hb
          norm_cast at hb
          use (max M N), (by simp [hM])
          simp [Real.dist_eq, hM]
          rw [lt_abs]
          left
          linarith
        . have := Sequence.lowerseq_neq_top a N hN
          tauto
        . rw [h1] at h
          simp at h
      . intro b hb
        obtain ⟨ b, rfl ⟩ | rfl | rfl := EReal.def b
        . simp at hb
          rw [lt_iff_exists_pos_add] at hb
          obtain ⟨ d, hd, rfl ⟩ := hb
          specialize h (d/2) (by linarith)
          rw [Real.eventuallyClose_def] at h
          obtain ⟨ N, hN, h ⟩ := h
          rw [Real.closeSeq_def] at h
          use a.lowerseq N
          constructor
          . simp
            use N
          suffices h : ((b+(d/2)):ℝ) ≤ a.lowerseq N
          . have : (b:EReal) < ((b+(d/2)):ℝ)
            . norm_cast
              linarith
            exact Std.lt_of_lt_of_le this h
          simp [lowerseq]
          intro b n hn hn2 rfl
          simp [hn, hn2]
          specialize h n (by simp [hn, hn2])
          simp [Real.dist_eq, hn, hn2] at h
          norm_cast
          rw [abs_le] at h
          linarith
        . tauto
        . use a.lowerseq a.m
          simp
          constructor
          . use a.m
          simp [lowerseq, inf]
          contrapose! hb
          rw [sInf_le_iff] at hb
          rw [Sequence.lim_eq] at h
          replace h := Sequence.bounded_of_cauchy (Sequence.IsCauchy.convergent h.1)
          rw [Sequence.bounded_iff] at h
          obtain ⟨ M, hM ⟩ := h.2
          contrapose! hb
          use M
          simp [lowerBounds]
          intro b n hn rfl
          simp [hn]
          exact hM n hn
    . sorry
  . exact tendsTo_if_eq_limsup_liminf_helper c h

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by
  simp [sup]
  intro b n hn rfl
  rw [le_sSup_iff]
  intro c hc
  simp [upperBounds] at hc
  specialize hc (a := b.seq n) n (by simp [← hm, hn]) (by rfl)
  specialize hab n hn
  replace hab : a.seq n ≤ ((b.seq n):EReal)
  . norm_cast
  exact EReal.trans hab hc

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
  simp [limsup]
  intro b n hn rfl
  rw [sInf_le_iff]
  intro c hc
  have h1 : c ≤ a.upperseq n
  . simp [lowerBounds] at hc
    exact hc (a := a.upperseq n) n (by omega) (by rfl)
  have h2 : a.upperseq n ≤ b.upperseq n
  . simp [upperseq]
    intro c m hm hm2 rfl
    simp [hm, hm2]
    have h1 : a.seq m ≤ ((b.seq m):EReal)
    . norm_cast
      apply hab
      exact hm
    have h2 : ((b.seq m):EReal) ≤ (b.from n).sup
    . simp [sup]
      rw [le_sSup_iff]
      intro c hc
      simp [upperBounds] at hc
      have hbm : b.m ≤ m := by omega
      exact hc (a := b.seq m) m hbm hm2 (by simp [hbm, hm2])
    exact EReal.trans h1 h2
  exact EReal.trans h1 h2

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by sorry

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hab: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: c.TendsTo L) :
    b.TendsTo L := by
  rw [Sequence.tendsTo_iff_eq_limsup_liminf] at *
  constructor
  . have h1 : a.liminf ≤ b.liminf
    . apply Sequence.liminf_mono
      . omega
      . intro n hn
        exact (hab n hn).1
    have h2 : b.liminf ≤ c.liminf
    . apply Sequence.liminf_mono
      . omega
      . intro n hn
        exact (hab n (by omega)).2
    rw [ha.1] at h1
    rw [hb.1] at h2
    exact le_antisymm h2 h1
  . sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  sorry

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  constructor <;> intro h
  . -- Squeeze test using a <= |a| <= max (-a, a).
    have h1 : (((-1:ℝ) • a) ⊔ a).TendsTo (0:ℝ)
    . have : (0:ℝ) = max 0 0 := by simp
      rw [this]; clear this
      apply Sequence.tendsTo_max
      . have : (0:ℝ) = -1 * 0 := by norm_num
        rw [this]; clear this
        apply Sequence.tendsTo_smul
        . exact h
      . exact h
    exact Sequence.lim_of_between (by {
      simp [max_m, smul_m]
    }) (by {
      intro n hn
      simp
      constructor
      . exact le_abs_self (a.seq n)
      simp [abs_le]
      contrapose! h
      linarith
    }) h h1
  . -- Squeeze test using -|a| <= a <= |a|.
    have h1 : (((-1:ℝ) • a.abs)).TendsTo (0:ℝ)
    . have : (0:ℝ) = -1 * 0 := by norm_num
      rw [this]; clear this
      apply Sequence.tendsTo_smul
      exact h
    exact Sequence.lim_of_between (by {
      simp [smul_m]
    }) (by {
      intro n hn
      simp
      constructor
      . exact neg_abs_le (a.seq n)
      exact le_abs_self (a.seq n)
    }) h1 h

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]
  use a.liminf.toReal; symm; apply coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  grind

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  use fun x ↦ x
  use fun x ↦ x+1
  constructor
  . intro n
    linarith
  simp [sup]
  intro b n hn rfl
  simp [hn]
  lift n to ℕ using hn
  simp
  rw [le_sSup_iff]
  intro b hb
  simp [upperBounds] at hb
  have hn : (0:ℤ) ≤ n + 1 := by omega
  exact hb (a := n+1) (n+1) hn (by simp [hn])

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use ((fun x:ℕ ↦ (-1:ℝ)):Sequence), ((-1:ℝ))
  left
  simp [Sequence.tendsTo_def]
  constructor
  . intro e he
    use 0
    simp
    intro n hn
    simp at hn
    simp [hn]
    linarith
  . use 1, (by norm_num)
    intro n hn
    use n, hn, (by simp)
    simp [hn, Real.dist_eq]
    norm_num

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by
  simp [ExtendedLimitPoint]
  obtain ⟨ r, hr ⟩ | h | h := EReal.def a.limsup
  . simp [← hr]
    apply Sequence.limit_point_of_limsup
    exact hr.symm
  . simp [h]
    intro r
    simp [limsup] at h
    rw [← isGLB_iff_sInf_eq, isGLB_iff_le_iff] at h
    replace h := (h ⊤).mp (by simp)
    simp [lowerBounds] at h
    replace h := h (a := a.upperseq a.m) a.m (by simp) (by rfl)
    simp [upperseq, sup] at h
    rw [le_sSup_iff] at h
    contrapose! h
    use r
    constructor
    . simp [upperBounds]
      intro b n hn rfl
      simp [hn]
      apply h
      exact hn
    . simp
  . simp [h]
    have h : ¬ (⊥:EReal) = ⊤ := by tauto
    simp [h]; clear h
    intro r
    simp [limsup] at h
    rw [sInf_eq_bot] at h
    obtain ⟨ b, hb, hbr ⟩ := h r (by simp); clear h
    simp at hb
    obtain ⟨ N, hN, rfl ⟩ := hb
    simp [upperseq, sup] at hbr
    have h := sSup_lt_iff_helper hbr (a.seq N) (by {
      simp
      use N
      simp [hN]
    })
    simp at h
    use N

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by sorry

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by
  obtain ⟨ r, rfl ⟩ | rfl | rfl := EReal.def L
  . simp [ExtendedLimitPoint] at h
    exact (Sequence.limit_point_between_liminf_limsup h).2
  . simp [ExtendedLimitPoint] at h
    simp [limsup]
    intro b n hn rfl
    simp [upperseq, sup]
    rw [le_sSup_iff]
    intro b hb
    simp [upperBounds] at hb
    contrapose! hb
    obtain ⟨ r, rfl ⟩ | rfl | rfl := EReal.def b
    . contrapose! h
      obtain ⟨ M, hM ⟩ := Sequence.finite_bounded_helper a n hn
      use max M r
      intro m hm
      obtain hm2 | hm2 := lt_or_ge m n
      . specialize hM m hm2
        rw [abs_le] at hM
        simp [hM]
      . specialize h (a.seq m) m hm hm2 (by simp [hm, hm2])
        simp at h
        simp [h]
    . simp at hb
    . use (a.seq n), n, hn, (by simp), (by simp [hn])
      simp
  . simp

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by sorry

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by
  -- 0, 1, -1, 0, 2, -2...
  sorry

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by
  rw [Sequence.limit_point_def] at ⊢ hbc
  intro e he N hN
  simp_rw [Sequence.limit_point_def] at hab
  -- There are infinitely many points where a is close to b n.
  -- Same for b close to c.
  specialize hbc (e/2) (by linarith) (max N b.m) (by simp)
  obtain ⟨ n, hn, hb ⟩ := hbc
  simp at hn
  specialize hab n hn.2 (e/2) (by linarith) (max N a.m) (by simp)
  obtain ⟨ m, hm, ha ⟩ := hab
  simp at hm
  use m, hm.1
  rw [abs_le] at *
  constructor <;> linarith


end Chapter6
