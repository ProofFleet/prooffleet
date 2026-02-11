import MoltResearch.Discrepancy.Basic

/-!
# Constant discrepancy lemmas

Lemmas about arithmetic progression sums of constant functions.
-/

namespace MoltResearch

lemma apSum_const (c : ℤ) (d n : ℕ) :
    apSum (fun _ => c) d n = n • c := by
  unfold apSum
  simp

lemma apSumOffset_const (c : ℤ) (d m n : ℕ) :
    apSumOffset (fun _ => c) d m n = n • c := by
  unfold apSumOffset
  simp

@[simp] lemma apSum_const_zero (d n : ℕ) :
    apSum (fun _ => (0 : ℤ)) d n = 0 := by
  simpa using (apSum_const (c := (0 : ℤ)) d n)

@[simp] lemma apSum_const_one (d n : ℕ) :
    apSum (fun _ => (1 : ℤ)) d n = n := by
  simpa using (apSum_const (c := (1 : ℤ)) d n)

@[simp] lemma apSumOffset_const_zero (d m n : ℕ) :
    apSumOffset (fun _ => (0 : ℤ)) d m n = 0 := by
  simpa using (apSumOffset_const (c := (0 : ℤ)) d m n)

@[simp] lemma apSumOffset_const_one (d m n : ℕ) :
    apSumOffset (fun _ => (1 : ℤ)) d m n = n := by
  simpa using (apSumOffset_const (c := (1 : ℤ)) d m n)

end MoltResearch
