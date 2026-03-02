import LeanBook.Logic.PredLogic

-- def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥→ idol
-- def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -♥→ tgt

example : IdolExists → EveryoneLovesSomeone := by
  -- IdolExists を仮定
  intro h
  -- idol : Human, h : ∀ (h : Human), h -♥→ idol
  obtain ⟨idol, h⟩ := h

  -- 定義より、⊢ ∀ h : Human, ∃ tgt : Human, h -♥→ tgt
  dsimp [EveryoneLovesSomeone]

  -- ∀ h : Human を仮定
  intro human

  -- ∃ tgt, human -♥→ idol を示せば良いが、
  -- tgt = idol とすれば良い
  exists idol

  -- ∵ human -♥→ idol が成り立つ
  exact h human

/-- 書籍の解答 -/
example : IdolExists → EveryoneLovesSomeone := by
  dsimp [EveryoneLovesSomeone]
  intro hidol h
  obtain ⟨idol, hidol⟩ := hidol
  exists idol
  exact hidol h
