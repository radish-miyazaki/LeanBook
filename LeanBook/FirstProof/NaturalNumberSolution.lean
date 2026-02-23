import LeanBook.FirstProof.NaturalNumber

/-- 右からゼロを足しても値は変わらない -/
example (n : MyNat) : MyNat.add n .zero = n := by
  rfl
