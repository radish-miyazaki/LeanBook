example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h hp
  cases h with
  | inl nhp => contradiction
  | inr nq => exact nq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h1
  -- ¬ (P ∨ Q) → ¬ P ∧ ¬ Q
  case mp =>
    constructor
    -- ⊢ ¬ P
    -- つまり、⊢ P → False
    case left =>
      intro hp -- ⊢ False
      apply h1 -- ⊢ P ∨ Q
      left     -- ⊢ P
      exact hp

    -- ⊢ ¬ Q
    -- つまり、⊢ Q → False
    case right =>
      intro hq -- ⊢ False
      apply h1 -- ⊢ P ∨ Q
      right    -- ⊢ Q
      exact hq

  -- ¬ P ∧ ¬ Q → ¬ (P ∨ Q)
  case mpr =>
    intro hpq
    cases hpq with
    -- ¬ P が成り立つ場合
    | inl hp =>
      -- h1.left : P → False という項が存在するため、⊢ False を証明するには、P を証明すれば十分
      apply h1.left
      exact hp
    -- ¬ Q が成り立つ場合
    | inr hq =>
      apply h1.right
      exact hq
