example (P : Prop) : ¬ (P ↔ ¬ P) := by
  -- P ↔ ¬ P（P → ¬ P / ¬ P → P） と仮定する
  intro h

  -- -- ここで ¬ P（P → False）が成り立つ
  have hnp : ¬ P := by
    -- P と仮定する
    intro hq
    -- ¬ P は成り立つ
    have : ¬ P := by
      -- rw のみだと、P → False の P が ¬ P に置き換わり、ゴールが ¬¬ P となる
      -- そこで、at を用いて仮定（hq）を ¬ P に置き換え
      rw [h] at hq
      exact hq
    contradiction

  -- また、P が成り立つ
  have : P := by
    rw [h]
    exact hnp

  -- これらは最初の前提と矛盾する
  contradiction
