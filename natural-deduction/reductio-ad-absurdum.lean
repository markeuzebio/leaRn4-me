-- Exemplos envolvendo redução ao absurdo

-- Lean4 não suporta, à priori, a regra de redução por absurdo
-- Por isso, utilizamos a biblioteca "Classical" que implementa a regra
open Classical

variable (A B : Prop)

theorem ex1 : ¬ (¬ A) → A :=
  by
    intro HnnA
    show A
    apply byContradiction
    intro HnA
    exact HnnA HnA

-- Este aqui foi realmente difícil para provar
theorem hard (H : A → B) : ¬ A ∨ B :=
  by
    apply byContradiction
    intro HnnAorB
    exact
    (
      HnnAorB
      (Or.inl
        (
          by
            intro HA
            show False
            exact
            (
              HnnAorB
              (Or.inr (H HA))
            )
        )
      )
    )
