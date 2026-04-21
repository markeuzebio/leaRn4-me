-- provas de exemplo usando conjunções.

-- Operador da conjunção: \and
-- Introdução da conjunção: And.intro
-- Eliminação à esquerda: And.left
-- Eliminação à direita: And.right

variable (A B C D : Prop)

theorem ex1 (H : A ∧ B) : B ∧ A :=
  And.intro
      -- B
      (And.right H)
      -- A
      (And.left H)

theorem ex2 (H : A ∧ (B ∧ C)) : (A ∧ B) ∧ C :=
  And.intro
      -- A ∧ B
      (And.intro 
          -- A
          (And.left H)
          -- B
          (And.left
              (And.right H)))
      -- C
      (And.right
        -- B ∧ C
        (And.right H))


theorem ex3 (H1 : A ∧ B)(H2 : C ∧ D) : B ∧ C :=
  And.intro
    -- B
    (And.right H1)
    -- C
    (And.left H2)