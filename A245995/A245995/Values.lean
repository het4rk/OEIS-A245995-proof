import A245995.Main

/-!
# Sanity checks

A few values of `T` checked by kernel evaluation (`decide +kernel`, no extra axioms) against
the OEIS data, confirming the transcription of the definition and its indexing.
-/
namespace A245995
/-- sanity checks against the OEIS data, by kernel evaluation -/
example : T 1 2 = 8 := by decide +kernel
example : T 2 3 = 68 := by decide +kernel
example : T 0 4 = 20 := by decide +kernel
end A245995
