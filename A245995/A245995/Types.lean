import A245995.Basic

/-!
# Pair types for OEIS A245995

`N k L x y` (good words of length `L+2` starting `x, y`) depends only on the type of the
pair `(x,y)`: forbidden (`y = rev x`), equal, first letter the middle `k/2`, second letter the
middle, or other. `N_eq_typ` proves this by induction, with the type counts `V k L` evolving by
an explicit linear step; `row_sum` and `card_rest` do the counting over `Fin (k+1)`.
-/

open Finset

namespace A245995

lemma add_eq_iff {k : ℕ} {x y : Fin (k + 1)} : (x : ℕ) + y = k ↔ y = x.rev := by
  rw [Fin.ext_iff, Fin.val_rev]
  have := x.isLt; have := y.isLt
  omega

lemma rev_eq_self_iff {k : ℕ} {x : Fin (k + 1)} : x.rev = x ↔ 2 * (x : ℕ) = k := by
  rw [Fin.ext_iff, Fin.val_rev]
  have := x.isLt
  omega

lemma mid_unique {k : ℕ} {x y : Fin (k + 1)} (hx : x.rev = x) (hy : y.rev = y) : x = y := by
  rw [rev_eq_self_iff] at hx hy
  exact Fin.ext (by omega)

lemma T_eq_sum (n k : ℕ) : T n k = ∑ x : Fin (k + 1), ∑ y : Fin (k + 1), N k n x y := by
  classical
  unfold T N
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 2) → Fin (k + 1) => w 0)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 2) → Fin (k + 1) => w 1)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1; ext w; simp [and_assoc]

lemma N_zero (k : ℕ) (x y : Fin (k + 1)) : N k 0 x y = if y = x.rev then 0 else 1 := by
  classical
  unfold N
  split_ifs with h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w _ ⟨hg, h0, h1⟩
    exact hg 0 1 (by simp) (by simp) (by rw [h0, h1, add_eq_iff]; exact h)
  · rw [Finset.card_eq_one]
    refine ⟨![x, y], ?_⟩
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨_, h0, h1⟩
      funext i; fin_cases i <;> simp [h0, h1]
    · rintro rfl
      refine ⟨?_, by simp, by simp⟩
      intro i j hij hji
      fin_cases i <;> fin_cases j <;> simp at hij
      simpa [add_eq_iff] using h

/-! ## The four-type invariant -/

variable (k : ℕ)

/-- number of self-complementary letters (1 if `k` even, else 0) -/
def eps : ℕ := (univ.filter (fun a : Fin (k + 1) => a.rev = a)).card

/-- value of `N` on a pair according to its type -/
def typ (E D P Q : ℤ) (x y : Fin (k + 1)) : ℤ :=
  if y = x.rev then 0 else if x = y then E else if x.rev = x then P
  else if y.rev = y then Q else D

/-- row value for a non-middle first letter -/
def R (E D Q : ℤ) : ℤ := E + (eps k : ℤ) * Q + ((k : ℤ) - 1 - eps k) * D

lemma card_rest (b : Fin (k + 1)) (hb : b.rev ≠ b) :
    ((univ.filter (fun a : Fin (k + 1) => ¬ (a = b.rev ∨ a = b ∨ a.rev = a))).card : ℤ)
      = (k : ℤ) + 1 - 2 - eps k := by
  classical
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin (k + 1))))
    (fun a : Fin (k + 1) => a = b.rev ∨ a = b ∨ a.rev = a)
  have h2 : (univ.filter (fun a : Fin (k + 1) => a = b.rev ∨ a = b ∨ a.rev = a)) =
      ({b.rev, b} : Finset _) ∪ univ.filter (fun a : Fin (k + 1) => a.rev = a) := by
    ext a; simp [or_assoc]
  have hd : Disjoint ({b.rev, b} : Finset (Fin (k + 1)))
      (univ.filter (fun a : Fin (k + 1) => a.rev = a)) := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    simp only [mem_filter, mem_univ, true_and]
    rcases ha with rfl | rfl
    · rw [Fin.rev_rev]; exact fun h => hb h.symm
    · exact hb
  have hne : b.rev ≠ b := hb
  rw [h2, Finset.card_union_of_disjoint hd, Finset.card_pair hne] at h1
  simp only [card_univ, Fintype.card_fin] at h1
  unfold eps
  omega

lemma row_sum (E D P Q : ℤ) (b : Fin (k + 1)) :
    ∑ a, typ k E D P Q b a = if b.rev = b then (k : ℤ) * P else R k E D Q := by
  classical
  split_ifs with hb
  · have : ∀ a, typ k E D P Q b a = if a = b then 0 else P := by
      intro a; unfold typ
      by_cases ha : a = b
      · simp [ha, hb]
      · simp [ha, hb, Ne.symm ha]
    simp only [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have := Finset.filter_ne' (univ : Finset (Fin (k + 1))) b
    simp only [ne_eq] at this
    rw [this, Finset.card_erase_of_mem (mem_univ _)]
    simp
  · have : ∀ a, typ k E D P Q b a = (if a = b then E else 0) + (if a.rev = a then Q else 0)
        + (if ¬ (a = b.rev ∨ a = b ∨ a.rev = a) then D else 0) := by
      intro a; unfold typ
      by_cases h1 : a = b.rev
      · subst h1
        have : ¬ b.rev.rev = b.rev := by rw [Fin.rev_rev]; exact fun h => hb h.symm
        simp [hb, Ne.symm hb]
      · by_cases h2 : a = b
        · subst h2; simp [hb, h1]
        · by_cases h3 : a.rev = a
          · simp [h1, h2, h3, Ne.symm h2, hb]
          · simp [h1, h2, h3, Ne.symm h2, hb]
    simp only [this, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' univ b, if_pos (mem_univ _)]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [card_rest k b hb]
    unfold R eps
    ring

/-- the four type-counts -/
def V : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 1, 1, 1)
  | L + 1 =>
    let v := V L
    (R k v.1 v.2.1 v.2.2.2, R k v.1 v.2.1 v.2.2.2 - v.2.1,
      R k v.1 v.2.1 v.2.2.2 - v.2.2.2, ((k : ℤ) - 1) * v.2.2.1)

lemma eps_eq_one {h : Fin (k + 1)} (hh : h.rev = h) : eps k = 1 := by
  unfold eps
  rw [Finset.card_eq_one]
  refine ⟨h, ?_⟩
  ext a; simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun ha => mid_unique ha hh, fun ha => ha ▸ hh⟩

theorem N_eq_typ (L : ℕ) (x y : Fin (k + 1)) :
    (N k L x y : ℤ) = typ k (V k L).1 (V k L).2.1 (V k L).2.2.1 (V k L).2.2.2 x y := by
  induction L generalizing x y with
  | zero =>
    rw [N_zero]; unfold typ; simp only [V]
    split_ifs <;> simp
  | succ L ih =>
    rw [N_succ]
    have hf : univ.filter (fun a : Fin (k + 1) => (x : ℕ) + a ≠ k) = univ.erase x.rev := by
      ext a; simp [add_eq_iff]
    split_ifs with hxy
    · rw [add_eq_iff] at hxy
      unfold typ; simp [hxy]
    · rw [add_eq_iff] at hxy
      rw [hf]; push_cast
      simp only [ih]
      rw [Finset.sum_erase_eq_sub (mem_univ _), row_sum]
      set E := (V k L).1; set D := (V k L).2.1; set P := (V k L).2.2.1; set Q := (V k L).2.2.2
      have hV : V k (L + 1) = (R k E D Q, R k E D Q - D, R k E D Q - Q, ((k : ℤ) - 1) * P) := rfl
      rw [hV]
      unfold typ
      simp only [if_neg hxy]
      by_cases hc : x = y
      · subst hc
        have hb : ¬ x.rev = x := fun h => hxy h.symm
        simp [hb]
      · simp only [if_neg hc]
        have h1 : ¬ x.rev = y.rev := fun h => hc (Fin.rev_injective h)
        have h2 : (x.rev.rev = x.rev) ↔ x.rev = x := by
          rw [Fin.rev_rev]; exact eq_comm
        simp only [h1, h2, if_false]
        by_cases hxm : x.rev = x
        · have hym : ¬ y.rev = y := fun h => hc (mid_unique hxm h)
          simp [hxm, hym]
        · by_cases hym : y.rev = y
          · simp [hxm, hym]; ring
          · simp [hxm, hym]

end A245995
