import A245995.Types

/-!
# Hardin's empirical column recurrences for OEIS A245995, proved

* `T_odd`  : for odd `k`,  `T(n+2,k) = (k-1) T(n+1,k) + T(n,k)`.
* `T_even` : for even `k ≥ 2`,
  `T(n+4,k) = (k-2) T(n+3,k) + T(n+2,k) + (k-1)^2 T(n+1,k) + (k-1) T(n,k)`.
* `T_col1` … `T_col9` : Hardin's nine column formulas, in OEIS indexing.
-/

open Finset

namespace A245995

lemma eps_odd {k : ℕ} (hk : Odd k) : eps k = 0 := by
  unfold eps
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ h
  rw [rev_eq_self_iff] at h
  obtain ⟨m, hm⟩ := hk
  omega

lemma eps_even {k : ℕ} (hk : Even k) : eps k = 1 := by
  obtain ⟨m, hm⟩ := hk
  refine eps_eq_one k (h := ⟨m, by omega⟩) ?_
  rw [rev_eq_self_iff]; simp; omega

/-- closed form of `T` in terms of the type counts -/
def F (k : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : ℤ :=
  (eps k : ℤ) * k * v.2.2.1 + ((k : ℤ) + 1 - eps k) * R k v.1 v.2.1 v.2.2.2

theorem T_eq_F (n k : ℕ) : (T n k : ℤ) = F k (V k n) := by
  classical
  rw [T_eq_sum]; push_cast
  simp only [N_eq_typ, row_sum]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin (k + 1))))
    (fun a : Fin (k + 1) => a.rev = a)
  simp only [card_univ, Fintype.card_fin] at h
  unfold F
  have : ((univ.filter (fun a : Fin (k + 1) => ¬ a.rev = a)).card : ℤ) = (k : ℤ) + 1 - eps k := by
    unfold eps; omega
  rw [this]; unfold eps; ring

lemma V_succ (k L : ℕ) : V k (L + 1) =
    (R k (V k L).1 (V k L).2.1 (V k L).2.2.2, R k (V k L).1 (V k L).2.1 (V k L).2.2.2 - (V k L).2.1,
      R k (V k L).1 (V k L).2.1 (V k L).2.2.2 - (V k L).2.2.2, ((k : ℤ) - 1) * (V k L).2.2.1) := rfl

theorem T_odd_int {k : ℕ} (hk : Odd k) (n : ℕ) :
    (T (n + 2) k : ℤ) = ((k : ℤ) - 1) * T (n + 1) k + T n k := by
  simp only [T_eq_F, V_succ]
  unfold F R; rw [eps_odd hk]; push_cast; ring

theorem T_even_int {k : ℕ} (hk : Even k) (n : ℕ) :
    (T (n + 4) k : ℤ) = ((k : ℤ) - 2) * T (n + 3) k + T (n + 2) k
      + ((k : ℤ) - 1) ^ 2 * T (n + 1) k + ((k : ℤ) - 1) * T n k := by
  simp only [T_eq_F, V_succ]
  unfold F R; rw [eps_even hk]; push_cast; ring

/-- Odd `k ≥ 1`: `T(n+2,k) = (k-1) T(n+1,k) + T(n,k)`. -/
theorem T_odd {k : ℕ} (hk : Odd k) (n : ℕ) :
    T (n + 2) k = (k - 1) * T (n + 1) k + T n k := by
  have h := T_odd_int hk n
  have : 1 ≤ k := hk.pos
  zify [this]; exact h

/-- Even `k ≥ 2`. -/
theorem T_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) (n : ℕ) :
    T (n + 4) k = (k - 2) * T (n + 3) k + T (n + 2) k
      + (k - 1) ^ 2 * T (n + 1) k + (k - 1) * T n k := by
  have h := T_even_int hk n
  have : 1 ≤ k := by omega
  zify [this, hk2]; exact h

/-- `k = 2` satisfies the shorter recurrence `T(n+3) = T(n+2) + T(n)`. -/
theorem T_two (n : ℕ) : T (n + 3) 2 = T (n + 2) 2 + T n 2 := by
  have h : (T (n + 3) 2 : ℤ) = T (n + 2) 2 + T n 2 := by
    simp only [T_eq_F, V_succ]
    unfold F R; rw [eps_even (by decide)]; push_cast; ring
  exact_mod_cast h

/-- `k = 1`: the column is constant. -/
theorem T_one (n : ℕ) : T (n + 1) 1 = T n 1 := by
  have h : (T (n + 1) 1 : ℤ) = T n 1 := by
    simp only [T_eq_F, V_succ]
    unfold F R; rw [eps_odd (by decide)]; push_cast; ring
  exact_mod_cast h

/-! ## Hardin's column formulas, verbatim (OEIS indexing, `a(n) = T(n,k)`). -/

theorem T_col1 (n : ℕ) (hn : 2 ≤ n) : T n 1 = T (n - 1) 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using T_one m

theorem T_col2 (n : ℕ) (hn : 4 ≤ n) : T n 2 = T (n - 1) 2 + T (n - 3) 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simpa using T_two m

theorem T_col3 (n : ℕ) (hn : 3 ≤ n) : T n 3 = 2 * T (n - 1) 3 + T (n - 2) 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using T_odd (k := 3) (by decide) m

theorem T_col4 (n : ℕ) (hn : 5 ≤ n) :
    T n 4 = 2 * T (n - 1) 4 + T (n - 2) 4 + 9 * T (n - 3) 4 + 3 * T (n - 4) 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simpa using T_even (k := 4) (by decide) (by norm_num) m

theorem T_col5 (n : ℕ) (hn : 3 ≤ n) : T n 5 = 4 * T (n - 1) 5 + T (n - 2) 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using T_odd (k := 5) (by decide) m

theorem T_col6 (n : ℕ) (hn : 5 ≤ n) :
    T n 6 = 4 * T (n - 1) 6 + T (n - 2) 6 + 25 * T (n - 3) 6 + 5 * T (n - 4) 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simpa using T_even (k := 6) (by decide) (by norm_num) m

theorem T_col7 (n : ℕ) (hn : 3 ≤ n) : T n 7 = 6 * T (n - 1) 7 + T (n - 2) 7 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using T_odd (k := 7) (by decide) m

theorem T_col8 (n : ℕ) (hn : 5 ≤ n) :
    T n 8 = 6 * T (n - 1) 8 + T (n - 2) 8 + 49 * T (n - 3) 8 + 7 * T (n - 4) 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simpa using T_even (k := 8) (by decide) (by norm_num) m

theorem T_col9 (n : ℕ) (hn : 3 ≤ n) : T n 9 = 8 * T (n - 1) 9 + T (n - 2) 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using T_odd (k := 9) (by decide) m

end A245995
