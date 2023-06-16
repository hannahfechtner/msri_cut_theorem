import MyProject.Definitions
import MyProject.Size

open sequent_calculus

theorem EX_more {Γ : List PropForm} {A : PropForm} : (⊥ :: Γ ⊢₁ A) := by
  have this : [] ++ [PropForm.fls] ++ [] ++ Γ ++ [] = PropForm.fls :: Γ := by
    simp
  rw [← this]
  apply Proof_CF.com
  simp
  apply Proof_CF.wek
  apply Proof_CF.exfal

theorem transport_CF {Γ Δ : List PropForm} {A : PropForm} : (Γ ++ Δ  ⊢₁ A) → (Δ ++ Γ ⊢₁ A)  := by
  intro h
  have this : [] ++ Δ  ++ [] ++ Γ  ++ [] = Δ  ++ Γ := by
    simp
  rw [← this]
  apply Proof_CF.com
  simp
  assumption

theorem triplet_left (Γ Δ Η : List PropForm) {A : PropForm} : (Γ ++ Δ ++ Η ⊢₁ A) → (Δ ++ Γ ++ Η ⊢₁ A)  := by
  intro h
  have this : [] ++ Δ  ++ [] ++ Γ  ++ Η = Δ  ++ Γ ++ Η := by
    simp
  rw [← this]
  apply Proof_CF.com
  simp
  have that : Γ ++ Δ ++ Η = Γ ++ (Δ ++ Η) := by simp
  rw [←that]
  assumption

lemma CF_C {Γ : List PropForm} {A : PropForm} : (Γ ⊢₁ A) → (Γ ⊢ A)
  | Proof_CF.id => Proof.id
  | Proof_CF.exfal => Proof.exfal
  | @Proof_CF.com Θ Λ Ξ C X Y D => @Proof.com Θ Λ Ξ C X Y (CF_C D)
  | @Proof_CF.wek Θ C Λ D => @Proof.wek Θ C Λ (CF_C D)
  | @Proof_CF.contr Θ C Λ D => @Proof.contr Θ C Λ (CF_C D)
  | Proof_CF.rimpl D => Proof.rimpl (CF_C D)
  | Proof_CF.limpl D E => Proof.limpl (CF_C D) (CF_C E)
  | Proof_CF.rconj D E => Proof.rconj (CF_C D) (CF_C E)
  | Proof_CF.lconjl D => Proof.lconjl (CF_C D)
  | Proof_CF.lconjr D => Proof.lconjr (CF_C D)
  | Proof_CF.rdisjl D => Proof.rdisjl (CF_C D)
  | Proof_CF.rdisjr D => Proof.rdisjr (CF_C D) 
  | Proof_CF.ldisj D E => Proof.ldisj (CF_C D) (CF_C E)

  -- intro h
  -- induction h
  -- . exact Proof.id 
  -- . exact Proof.exfal
  -- . rename_i ih
  --   apply Proof.com
  --   exact ih 
  -- . rename_i ih
  --   apply Proof.wek
  --   exact ih
  -- . rename_i ih
  --   apply Proof.contr
  --   exact ih
  -- . rename_i ih
  --   apply Proof.rimpl
  --   exact ih
  -- . rename_i ih1 ih2
  --   apply Proof.limpl
  --   . exact ih1 
  --   exact ih2
  -- . rename_i ih1 ih2
  --   apply Proof.rconj
  --   . exact ih1
  --   exact ih2
  -- . rename_i ih
  --   apply Proof.lconjl
  --   exact ih
  -- . rename_i ih
  --   apply Proof.lconjr
  --   exact ih
  -- . rename_i ih
  --   apply Proof.rdisjl
  --   exact ih
  -- . rename_i ih
  --   apply Proof.rdisjr
  --   exact ih
  -- . rename_i ih1 ih2
  --   apply Proof.ldisj
  --   . exact ih1
  --   exact ih2
  
-- theorem my_attempt (Γ : List PropForm) (P : PropForm) (A B C D E : List PropForm) :
--  (P :: Γ = A ++ B ++ C ++ D ++ E) → 
-- ((P ∈ A) ∨ (P ∈ B) ∨ (P ∈ C) ∨ (P ∈ D) ∨ (P ∈ E)) := by 
--   intro h 
--   induction A 
--   sorry
--   sorry

theorem or_principal_left {Γ₁ Γ₂ : List PropForm} 
    {A B D : PropForm} : (Γ₁ ⊢ A) -> ([(A ∨ B)] ++ Γ₂ ⊢ D) -> 
       (Γ₁++Γ₂ ⊢₁ D):= by sorry
  -- intro d
  -- generalize h' : [(A ∨ B)] ++ Γ₂ = Δ 
  -- -- generalize h'' : D=G
  -- -- generalize h''' : Γ₂=Δ 
  -- intro e
  -- revert h'
  -- -- revert h''
  -- -- revert h'''generalize h'' : D=G
  -- --generalize h''' : Γ₂=Δ 
  -- cases e
  -- . intro ih
  --   have this : D = A ∨ B := by sorry
  --   rw [this]
  --   have that : [] ++ Γ₁ ++ [] ++ Γ₂ ++ [] = Γ₁ ++ Γ₂ := by simp
  --   rw [← that]
  --   apply Proof_CF.com
  --   simp
  --   apply Proof_CF.wek Γ₂ 
  --   apply Proof_CF.rdisjl
  --   exact hauptschatz d
    
  



def rimpl_inv {Γ : List PropForm} {A B : PropForm} (D : Γ ⊢ A → B) : A :: Γ ⊢ B := by
  sorry
  -- cases D 
  -- . apply @Proof.com [] [] [] _ [_] [_]
  --   apply Proof.limpl
  --   . apply Proof.id
  --   . apply @Proof.com [] [] [] _ [_] [_]
  --     simp
  --     apply Proof.wek [A] Proof.id
  -- . apply Proof.wek [A] Proof.exfal
  -- . rename_i a b c d e f
  --   apply @Proof.com ([A] ++ a) b c _ d e (rimpl_inv f) 
  -- . rename_i a b c
  --   apply @Proof.com [] [] a _ b [A] 
  --   simp
  --   apply Proof.wek b (rimpl_inv c)
  -- . rename_i a b c 
  --   --this is ridiculus 
  --   have deq : [] ++ [A] ++ [] ++ (b ++ a) ++ [] = A :: (b ++ a) := by 
  --     simp
  --   rw [← deq]  
  --   apply Proof.com
  --   simp
  --   apply Proof.contr
  --   have deq1 : [] ++ (b ++ b ++ a) ++ [] ++ [A] ++ [] = b ++ b ++ (a ++ [A]) := by
  --     simp
  --   rw [← deq1]  
  --   apply Proof.com [A] (b ++ b ++ a) 
  --   simp at c
  --   simp
  --   apply rimpl_inv c
  -- . assumption
  -- . rename_i a b c d e
  --   change [] ++ [A] ++ [] ++ [b → c] ++ a ⊢ B
  --   apply Proof.com
  --   apply Proof.limpl
  --   . apply Proof.wek [A] d
  --   . simp
  --     change [] ++ [c] ++ [] ++ [A] ++ a ⊢ B
  --     apply Proof.com
  --     apply rimpl_inv e
  -- . rename_i a b c d
  --   change [] ++ [A] ++ [] ++ [a ∧ c] ++ b ⊢ B
  --   apply Proof.com
  --   apply Proof.lconjl
  --   simp
  --   change [] ++ [a] ++ [] ++ [A] ++ b ⊢ B
  --   apply Proof.com
  --   apply rimpl_inv d 
  -- . rename_i a b c d
  --   change [] ++ [A] ++ [] ++ [c ∧ a] ++ b ⊢ B
  --   apply Proof.com
  --   apply Proof.lconjr
  --   simp
  --   change [] ++ [a] ++ [] ++ [A] ++ b ⊢ B
  --   apply Proof.com
  --   apply rimpl_inv d 
  -- . rename_i a b c d f
  --   change [] ++ [A] ++ [] ++ [a ∨ c] ++ b ⊢ B
  --   apply Proof.com
  --   apply Proof.ldisj
  --   . simp
  --     change [] ++ [a] ++ [] ++ [A] ++ b ⊢ B
  --     apply Proof.com
  --     apply rimpl_inv d 
  --   . simp
  --     change [] ++ [c] ++ [] ++ [A] ++ b ⊢ B
  --     apply Proof.com
  --     apply rimpl_inv f 
  -- . rename_i a b c e f 
  --   change [] ++ [A] ++ [] ++ a ++ c ⊢ B
  --   apply Proof.com
  --   have deq1 : [] ++ a ++ [] ++ [A] ++ c = a ++ (A :: c) := by
  --     simp
  --   rw [deq1]
  --   apply @Proof.cut _ b _ _
  --   . assumption
  --   . change [] ++ [b] ++ [] ++ [A] ++ c ⊢ B 
  --     apply Proof.com
  --     apply rimpl_inv f
  -- termination_by rimpl_inv D => Proof_size D    

def rconj_inv {Γ : List PropForm} {A B : PropForm} : (Γ ⊢ A ∧ B) → ((Γ ⊢ A) × (Γ ⊢ B))
:= by sorry
-- := by sorry
  -- | Proof.id => (Proof.lconjl (@Proof.id A), Proof.lconjr (@Proof.id B))
  -- | Proof.exfal => (@Proof.exfal A, @Proof.exfal B)
  -- | Proof.com X Y D => by
  --   constructor 
  --   . apply Proof.com 
  --     apply (rconj_inv D).1
  --   . apply Proof.com 
  --     apply (rconj_inv D).2
  -- | Proof.wek X D => (Proof.wek X (rconj_inv D).1, Proof.wek X (rconj_inv D).2)
  -- | Proof.contr X D => (Proof.contr X (rconj_inv D).1, Proof.contr X (rconj_inv D).2)
  -- | Proof.rimpl D => by 
    

                                  

def ldisj_inv {Γ : List PropForm} {A B C: PropForm} : ((A ∨ B) :: Γ ⊢ C) → ((A :: Γ ⊢ C) × (B :: Γ ⊢ C)) := by
  sorry  


