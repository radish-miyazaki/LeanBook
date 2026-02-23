-- #reduce / #check の結果表示にフィールド記法を使わないよう設定
set_option pp.fieldNotation.generalized false

/-- 自前実装した自然数 -/
inductive MyNat where
  /-- ゼロ -/
  | zero
  /-- 後者関数（n に対して n + 1 を返す） -/
  | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ
#check MyNat.succ .zero

/-- 自前実装した自然数の 1 -/
def MyNat.one := MyNat.succ .zero
/-- 自前実装した自然数の 2 -/
def MyNat.two := MyNat.succ .one

/-- MyNat の加算 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => succ (add m n)

#check MyNat.add .one .one = .two

#reduce MyNat.add .one .one
#reduce MyNat.two

/-- 1 + 1 = 2 の証明-/
example : MyNat.add .one .one = .two := by
  rfl
