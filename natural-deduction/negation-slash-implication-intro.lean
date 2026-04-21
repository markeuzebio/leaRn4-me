-- Exemplos de implicação.

variable (A B C : Prop)

-- [Provando C]
-- 1. Eliminação da implicação (Γ |- B → C   Γ |- B)
  -- [Provando Γ |- B → C]
  -- 1.1 Identidade (B → C)
  -- [Provando Γ |- B]
  -- 1.2 Eliminação da implicação (Γ |- A → B   Γ |- A)
    -- [Provando Γ |- A → B]
    -- 1.2.1 Identidade (A → B)
    -- [Provando Γ |- A]
    -- 1.2.2 Identidade (A)
theorem ex1 (H1 : A → B)
            (H2 : B → C)
            (H3 : A) : C :=
  show C
  from (H2 (show B
            from H1 H3))

-- [Provando A → C]
-- 1. Introdução da implicação (Γ ⋃ {A}   Γ |- C)
-- [Provando C]
-- 2. Eliminação da implicação (Γ |- B → C     Γ |- B)
  -- [Provando Γ |- B → C]
    -- 2.1. Identidade (B → C)
    -- [Provando Γ |- B]
    -- 2.2. Eliminação da implicação (Γ |- A → B    Γ |- A)
      -- [Provando Γ |- A → B]
      -- 2.2.1. Identidade (A → B)
      -- [Provando Γ |- A]
      -- 2.2.2. Identidade (A ∈ Γ) pela introdução no item 1.
theorem ex2 (H1 : A → B)
            (H2 : B → C) : A → C :=
  by
    intro HA
    show C
    exact (H2 (show B
               from H1 HA))

-- [Provando ¬ A (¬ A ≃ A → False)]
-- 1. Introdução da implicação (Γ ⋃ {A}    Γ |- False)
-- [Provando False]
-- 2. Eliminação da implicação (Γ |- B → False    Γ |- B)
  -- [Provando Γ |- B → False]
  -- 2.1 Identidade (¬ B)
  -- [Provando Γ |- B]
  -- 2.1.1 Eliminação da implicação (Γ |- A → B   Γ |- A)
    -- [Provando Γ |- A → B]
    -- 2.1.1.1. Identidade (Γ |- A → B)
    -- [Provando Γ -| A]
    -- 2.1.1.2. Identidade (A ∈ Γ) pela introdução no item 1.
theorem ex3 (H1 : A → B)
            (H2 : ¬ B) : ¬ A :=
  by
    intro HA
    show False
    exact (H2 (show B
               from H1 HA))
