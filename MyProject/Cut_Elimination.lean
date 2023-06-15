import Mathlib.Data.Real.Basic

inductive SEQ : List Prop → Prop → Prop where
  | Id : SEQ [A] A
  | Exfal : SEQ [False] A
  | Com : SEQ (List.join [Γ, [A, B], Δ]) C →  SEQ (List.join [Γ, [B, A], Δ]) C 
  | Wek : SEQ Γ A → SEQ ([B] ++ Γ) A
  | Contr : SEQ (Γ ++ [A, A]) B → SEQ (Γ ++ [A]) B
  | rImp : SEQ (Γ ++ [A]) B → SEQ Γ (A → B)
  | lImp : SEQ Γ A →  SEQ (Γ ++ [B]) C  → SEQ (Γ ++ [A → B]) C
  | rAnd : SEQ Γ A → SEQ Γ B → SEQ Γ (A ∧ B)
  | lAndl : SEQ (Γ ++ [A]) C  → SEQ (Γ ++ [A ∧ B]) C
  | lAndr : SEQ (Γ ++ [B]) C  → SEQ (Γ ++ [A ∧ B]) C
  | rOrl : SEQ Γ A  → SEQ Γ (A ∨ B)
  | rOrr : SEQ Γ B  → SEQ Γ (A ∨ B)
  | lOr : SEQ (Γ ++ [A]) C  → SEQ (Γ ++ [B]) C → SEQ (Γ ++ [A ∨ B]) C 
  | Cut : SEQ Γ A →  SEQ (Γ ++ [A]) B → SEQ Γ B 

inductive SEQ_CF : List Prop → Prop → Prop where
  | Id : SEQ_CF [A] A
  | Exfal : SEQ_CF [False] A
  | Com : SEQ_CF (List.join [Γ, [A, B], Δ]) C →  SEQ_CF (List.join [Γ, [B, A], Δ]) C 
  | Wek : SEQ_CF Γ A → SEQ_CF ([B] ++ Γ) A
  | Contr : SEQ_CF (Γ ++ [A, A]) B → SEQ_CF (Γ ++ [A]) B
  | rImp : SEQ_CF (Γ ++ [A]) B → SEQ_CF Γ (A → B)
  | lImp : SEQ_CF Γ A →  SEQ_CF (Γ ++ [B]) C  → SEQ_CF (Γ ++ [A → B]) C
  | rAnd : SEQ_CF Γ A → SEQ Γ B → SEQ_CF Γ (A ∧ B)
  | lAndl : SEQ_CF (Γ ++ [A]) C  → SEQ_CF (Γ ++ [A ∧ B]) C
  | lAndr : SEQ_CF (Γ ++ [B]) C  → SEQ_CF (Γ ++ [A ∧ B]) C
  | rOrl : SEQ_CF Γ A  → SEQ_CF Γ (A ∨ B)
  | rOrr : SEQ_CF Γ B  → SEQ_CF Γ (A ∨ B)
  | lOr : SEQ_CF (Γ ++ [A]) C  → SEQ_CF (Γ ++ [B]) C → SEQ_CF (Γ ++ [A ∨ B]) C 

infixl: 40 
  " ⊢ " => SEQ

infixl: 40 
  " ⊢₁ " => SEQ_CF


variable (P Q : Prop ) 

example : [P] ⊢ P := SEQ.Id

example : [P,P → Q] ⊢ Q := by 
  change [P] ++ [P→Q] ⊢ _


  apply SEQ.lImp 
  exact SEQ.Id
  apply SEQ.Wek 
  apply SEQ.Id

example : [P → ⊥, P ∨ Q] ⊢ Q := by 
  change [P → ⊥] ++ _ ⊢ _
  apply SEQ.lOr 
  . change List.join [[], [P → ⊥], [P], []] ⊢ _ 
    apply SEQ.Com
    change [P] ++ _ ⊢ _
    apply SEQ.lImp
    apply SEQ.Id
    apply SEQ.Wek
    apply SEQ.Exfal
  . apply SEQ.Wek
    apply SEQ.Id 

inductive  Var_Prop : ℕ → Prop where 

theorem Soundness (A : Prop) : [] ⊢ A → A  := by 
  sorry 

theorem Hauptsatz (Γ : List Prop) (A : Prop) : Γ ⊢ A → Γ ⊢₁ A := by 
  sorry 
