import Mathlib

open List

/-- Length distributes over list append.

Proof pattern: this is exactly the simp lemma `List.length_append`, so `simp` closes it;
under the hood it is an induction on the first list.
-/
theorem T1_09 {α} (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length := by
  simp
