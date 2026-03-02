/--（Lean標準の） 自然数上の述語 -/
def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  -- x : Nat が任意に与えられたとする
  intro x
  -- P を展開すれば明らか
  dsimp [P]

/-- すべての自然数 x について P x が成り立つなら、P 0 も成り立つ -/
example (P : Nat → Prop) (h : ∀ x :Nat, P x) : P 0 := by
  exact h 0

/-- 偶数であることを表す述語 -/
def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

example : even 4 := by
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x) : ∃ x : α, Q x := by
  -- 仮定 h が存在を主張している y を取り出す
  obtain ⟨y, hy⟩ := h
  -- この y が求めるものである
  exists y
  -- ∵ P y ∧ Q y が成り立つ
  exact hy.right

opaque Human : Type
opaque Love : Human → Human → Prop
@[inherit_doc] infix:50 " -♥→ " => Love

def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥→ idol
def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -♥→ tgt

#check ∃ philan : Human, ∀ h : Human, philan -♥→ h
def PhilanExists : Prop := ∃ philan, ∀ h : Human, philan -♥→ h

#check ∀ h : Human, ∃ lover, lover -♥→ h
def EveryoneLoved : Prop := ∀ h : Human, ∃ lover, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  -- 博愛主義者の存在を仮定
  intro h

  -- 存在が主張されている博愛主義者を philan とする
  -- この時、定義から h : ∀ human : Human, philan -♥→ human が成り立つ
  obtain ⟨philan, h⟩ := h

  -- この時 EveryoneLoved を示したい
  -- 定義より、∀ h : Human, ∃ lover, lover -♥→ h を示せば良い
  dsimp [EveryoneLoved]

  -- 任意に human : Human が与えられたとする
  intro human

  -- この時 ∃ lover : Human, lover -♥→ human を示したいが、
  -- これは philan である
  exists philan

  -- ∵ philan -♥→ human が成り立つから
  exact h human
