example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h hp
  cases h with
  | inl nhp => contradiction
  | inr nq => exact nq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h1
  -- ¬ (P ∨ Q) → ¬ P ∧ ¬ Q
  case mp =>
    -- ¬ P と ¬ Q のいずれかがゴールであれば、P または Q を仮定すれば、
    -- どちらのケースも ⊢ False となる
    constructor <;> intro h2
    case left =>
      apply h1 -- ⊢ P ∨ Q
      left     -- ⊢ P
      exact h2
    case right =>
      apply h1 -- ⊢ P ∨ Q
      right    -- ⊢ Q
      exact h2

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
