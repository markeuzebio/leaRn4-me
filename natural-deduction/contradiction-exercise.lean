-- Exemplo envolvendo a regra de contradição

variable (A B : Prop)

-- False.elim: Representa a regra de contradição
theorem ex1 (H1 : A ∨ B)
            (H2 : ¬ A) : B :=
  Or.elim H1
  (
    by
      intro HA
      show B
      exact
      (
        False.elim (H2 HA)
      )
  )
  (
    by
      intro HB
      show B
      exact HB
  )
