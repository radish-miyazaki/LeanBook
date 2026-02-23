#check Prop

#check (1 + 1 = 3 : Prop)

#check (fun n => n + 3 = 39 : Nat -> Prop)

#check True
#check False

example : True := by trivial

example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  apply hp

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

example (P Q : Prop) (hq : Q) : P → Q := by
  intro hp
  exact hq

#eval ¬ True
#eval ¬ False

example (P : Prop) : (¬ P) = (P → False) := by
  rfl

/-- P と ¬ P が同時に仮定すると矛盾する -/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  -- ¬ P は P → False に等しいので、P を示せば良い
  apply hnp
  exact hp

/-- 対偶が元の命題と同値であることの、片方のケース -/
example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  -- Q → ¬ P を示したいので Q を仮定する
  intro hq
  -- ¬ P は P → False に等しいので、P を仮定する
  intro hp
  -- h : P → Q → False に適用して False を得る
  exact h hp hq


example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

example (P : Prop) (hnp : ¬ P) (hp : P) : True := by
  contradiction

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  exfalso
  contradiction

#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor

  -- (Q → P) → P を証明する
  case mp =>
    intro h
    exact h hq

  -- P → Q → P を証明する
  case mpr =>
    intro hp hq
    exact hp

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h
  case mp =>
    exact h hq

  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- P ↔ Q が仮定にあるので、P の代わりに Q を示す
  rw [h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

#eval True ∨ True
#eval True ∨ False
#eval False ∨ True
#eval False ∨ False

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq
