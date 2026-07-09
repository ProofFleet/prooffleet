import Mathlib

open List

theorem T1_10 {α} (xs : List α) : xs.map (fun x => x) = xs := by
  simp
