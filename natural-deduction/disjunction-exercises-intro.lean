-- Exemplos envolvendo disjunção

variable (A B C : Prop)

-- Or.intro_left: recebe dois argumentos:
  -- 1. A fórmula que está à direita do ∨
  -- 2. O lado esquerdo, o qual se deve provar
theorem ex1 (H : A ∧ B) : A ∨ B :=
  (Or.intro_left B (And.left H))

-- OUTRA POSSÍVEL DEMONSTRAÇÃO
-- Or.intro_left: recebe dois argumentos:
  -- 1. A fórmula que está à direita do ∨
  -- 2. O lado esquerdo, o qual se deve provar
theorem ex1_1 (H : A ∧ B) : A ∨ B :=
  Or.intro_right A (And.right H)

-- Or.elim: recebe tres argumentos:
  -- 1. A fórmula da disjunção
  -- 2. A prova de que, com a inclusão do lado esquerdo da disjunção como hipótese, é dedutível
  -- 3. A prova de que, com a inclusão do lado direito da disjunção como hipótese, é dedutível
theorem ex2 (H1 : A ∨ B)
            (H2 : A → C)
            (H3 : B → C) : C :=
  Or.elim H1
          (
            by
              intro HA
              show C
              exact (H2 HA)
          )
          (
            by
              intro HB
              show C
              exact (H3 HB)
          )


theorem ex3 (H : (A ∧ B) ∨ (A ∧ C)) : B ∨ C :=
  Or.elim H
          (
            by
              intro HAandB
              show B ∨ C
              exact (Or.intro_left C (And.right HAandB)))
          (
            by
              intro HAandC
              show B ∨ C
              exact (Or.intro_right B (And.right HAandC))
          )
