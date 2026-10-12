import Mathlib

/-!
# OEIS A245995: definitions and the one-step extension lemma

`T n k` is the number of length `n+2` arrays over `0..k` with no pair among any
three consecutive terms summing to exactly `k` (R. H. Hardin, OEIS A245995).
-/

open Finset

namespace A245995

/-- Hardin's condition: no two entries at distance 1 or 2 sum to `k`. -/
def Good (k : ℕ) {m : ℕ} (w : Fin m → Fin (k + 1)) : Prop :=
  ∀ i j : Fin m, i.val < j.val → j.val ≤ i.val + 2 → (w i : ℕ) + (w j : ℕ) ≠ k

instance (k m : ℕ) : DecidablePred (@Good k m) := fun w => by
  unfold Good; infer_instance

/-- OEIS A245995: `T(n,k)` = number of length `n+2` arrays over `0..k` with no pair in any
consecutive three terms totalling exactly `k`. -/
def T (n k : ℕ) : ℕ :=
  (univ.filter (fun w : Fin (n + 2) → Fin (k + 1) => Good k w)).card

/-- Good words of length `L+2` whose first two letters are `x, y`. -/
def N (k L : ℕ) (x y : Fin (k + 1)) : ℕ :=
  (univ.filter (fun w : Fin (L + 2) → Fin (k + 1) => Good k w ∧ w 0 = x ∧ w 1 = y)).card

lemma good_cons {k L : ℕ} (c : Fin (k + 1)) (v : Fin (L + 2) → Fin (k + 1)) :
    Good k (Fin.cons c v : Fin (L + 3) → Fin (k + 1)) ↔
      Good k v ∧ (c : ℕ) + v 0 ≠ k ∧ (c : ℕ) + v 1 ≠ k := by
  constructor
  · intro h
    refine ⟨fun i j hij hji => ?_, ?_, ?_⟩
    · have := h i.succ j.succ (by simp [Fin.val_succ]; omega) (by simp [Fin.val_succ]; omega)
      simpa using this
    · have := h 0 (Fin.succ 0) (by simp) (by simp)
      simpa using this
    · have := h 0 (Fin.succ 1) (by rw [Fin.val_succ, Fin.val_one]; simp)
        (by rw [Fin.val_succ, Fin.val_one]; simp)
      rwa [Fin.cons_zero, Fin.cons_succ] at this
  · rintro ⟨hv, h0, h1⟩ i j hij hji
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hj : j.val = 0 ∨ j.val = 1 := by simp [Fin.val_succ] at hji; omega
        rcases hj with hj | hj
        · have : j = 0 := Fin.ext hj
          subst this; exact h0
        · have : j = 1 := Fin.ext (by simp [hj])
          subst this; exact h1
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact hv i j (by simpa [Fin.val_succ] using hij) (by simp [Fin.val_succ] at hji; omega)

lemma N_succ (k L : ℕ) (c b : Fin (k + 1)) :
    N k (L + 1) c b = if (c : ℕ) + b = k then 0 else
      ∑ a ∈ univ.filter (fun a : Fin (k + 1) => (c : ℕ) + a ≠ k), N k L b a := by
  classical
  have step1 : N k (L + 1) c b =
      (univ.filter (fun v : Fin (L + 2) → Fin (k + 1) =>
        Good k v ∧ v 0 = b ∧ (c : ℕ) + b ≠ k ∧ (c : ℕ) + v 1 ≠ k)).card := by
    unfold N
    refine Finset.card_bij' (fun w _ => Fin.tail w) (fun v _ => Fin.cons c v) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨hg, h0, h1⟩ := hw
      rw [← Fin.cons_self_tail w, good_cons] at hg
      refine ⟨hg.1, ?_, ?_, ?_⟩
      · simpa [Fin.tail] using h1
      · have := hg.2.1; rw [h0] at this; simpa [Fin.tail, ← h1] using this
      · have := hg.2.2; rw [h0] at this; exact this
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      obtain ⟨hg, h0, h1, h2⟩ := hv
      refine ⟨(good_cons c v).2 ⟨hg, by rw [h0]; exact h1, h2⟩, by simp, ?_⟩
      show (Fin.cons c v : Fin (L + 3) → Fin (k + 1)) 1 = b
      rw [← Fin.succ_zero_eq_one, Fin.cons_succ]; exact h0
    · intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw
      rw [← hw.2.1]; exact Fin.cons_self_tail w
    · intro v _
      funext i; simp [Fin.tail]
  rw [step1]
  split_ifs with hcb
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _ h; exact h.2.2.1 hcb
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun v => v 1)
      (t := univ.filter (fun a : Fin (k + 1) => (c : ℕ) + a ≠ k))]
    · refine Finset.sum_congr rfl (fun a ha => ?_)
      simp only [mem_filter, mem_univ, true_and] at ha
      unfold N
      congr 1
      ext v
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hg, h0, _, _⟩, h1⟩; exact ⟨hg, h0, h1⟩
      · rintro ⟨hg, h0, h1⟩
        refine ⟨⟨hg, h0, hcb, ?_⟩, h1⟩
        rw [h1]; exact ha
    · intro v hv
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
      exact hv.2.2.2

end A245995
