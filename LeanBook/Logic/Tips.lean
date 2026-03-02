/-- 三重否定の簡略化 -/
example (P : Prop) : ¬¬¬ P → ¬ P := by
  -- ¬¬¬ P かつ P を仮定する
  intro hn3p hp

  -- ここで ¬¬ P を補題とする
  have h2p : ¬¬ P := by
    -- ¬ P を仮定する
    intro hnp
    -- P と ¬ P で矛盾しているので証明終了
    contradiction

  -- ¬¬¬ P と ¬¬ P は矛盾しているので証明終了
  contradiction

example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  have : ¬¬ P := by
    intro hnp
    contradiction

  guard_hyp this : ¬¬ P

  contradiction

/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  -- ¬ (P ∨ ¬ P) と仮定する
  intro h

  -- ¬ P を示せば十分である
  suffices hyp : ¬ P from by
    -- ∵ ¬ P が成り立つなら、P ∨ ¬ P が成り立つため
    have : P ∨ ¬ P := by
      right
      exact hyp
    -- これは最初の仮定と矛盾する
    contradiction

  -- 以下、¬ P を示す
  guard_target =ₛ ¬ P

  -- P であると仮定する
  intro hq

  -- この時、P ∨ ¬ P が成り立つ
  have : P ∨ ¬ P := by
    left
    exact hq

  -- これは最初の仮定と矛盾する
  contradiction

example (P : Prop) : (P → True) ↔ True := by
  exact?

example (P : Prop) : (True → P) ↔ P := by
  exact?

example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

example : P → P := by
  intro hp
  exact hp
