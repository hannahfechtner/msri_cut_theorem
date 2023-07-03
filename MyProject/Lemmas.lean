import MyProject.Definitions
import MyProject.Properties
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

--Canonical embedding from Proof_CF to Proof.

lemma CF_C {Γ : List PropForm} {A : PropForm} : (Γ ⊢₁ A) → (Γ ⊢ A)
  | Proof_CF.id => Proof.id
  | Proof_CF.exfal => Proof.exfal
  | @Proof_CF.com Θ Λ Ξ C X Y p => @Proof.com Θ Λ Ξ C X Y (CF_C p)
  | @Proof_CF.wek Θ C Λ p => @Proof.wek Θ C Λ (CF_C p)
  | @Proof_CF.contr Θ C Λ p => @Proof.contr Θ C Λ (CF_C p)
  | Proof_CF.rimpl p => Proof.rimpl (CF_C p)
  | Proof_CF.limpl p q => Proof.limpl (CF_C p) (CF_C q)
  | Proof_CF.rconj p q => Proof.rconj (CF_C p) (CF_C q)
  | Proof_CF.lconjr p => Proof.lconjr (CF_C p)
  | Proof_CF.lconjl p => Proof.lconjl (CF_C p)
  | Proof_CF.rdisjr p => Proof.rdisjr (CF_C p) 
  | Proof_CF.rdisjl p => Proof.rdisjl (CF_C p)
  | Proof_CF.ldisj p q => Proof.ldisj (CF_C p) (CF_C q)

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

def rimpl_inv {Γ : List PropForm} {A B : PropForm} : (Γ ⊢ A → B) →  ([A] ++ Γ ⊢ B)
  | Proof.id => by
    change [] ++ [A] ++ [] ++ [A → B] ++ [] ⊢ B
    apply Proof.com
    apply Proof.limpl
    . apply Proof.id
    . apply @Proof.com [] [] [] _ [_] [_]
      simp [List.append_assoc]
      apply Proof.wek [A]
      apply Proof.id
  | Proof.exfal => Proof.wek [A] (@Proof.exfal B)
  | @Proof.com U V W _ X Y p => by
    have : Proof_size p < Proof_size (Proof.com X Y p) := by
      simp [Proof_size]
    change (A :: U) ++ Y ++ V ++ X ++ W ⊢ B   
    apply @Proof.com (A :: U) V W B X Y (rimpl_inv p) 
  | @Proof.wek X _ Y p => by
    have : Proof_size p < Proof_size (Proof.wek Y p) := by
      simp [Proof_size]
    change [] ++ [A] ++ [] ++ Y ++ X ⊢ B
    apply Proof.com
    simp [List.append_assoc]
    apply Proof.wek Y (rimpl_inv p)
  | @Proof.contr Y _ X p => by 
    change [] ++ [A] ++ [] ++ X ++ Y ⊢ B
    have h : (X ++ X ++ Y ⊢ A → B) = (X ++ (X ++ Y) ⊢ A → B) := by
      simp [List]
    have : Proof_size (cast h p) < Proof_size (Proof.contr X p) := by
      rw [cast_same_size h]
      simp [Proof_size]
    apply Proof.com
    simp [List.append_assoc]
    apply Proof.contr  
    have this : [] ++ (X ++ X) ++ [] ++ [A] ++ Y = X ++ X ++ A :: Y := by
       simp
    rw [←this]
    apply Proof.com
    simp [List.append_assoc]
    simp at p
    apply rimpl_inv p
  | Proof.rimpl p => p
  | @Proof.limpl X P Q _ p q => by 
    have : Proof_size q < Proof_size (Proof.limpl p q) := by
      simp [Proof_size]
      linarith 
    change [] ++ [A] ++ [] ++ [P → Q] ++ X ⊢ B
    apply Proof.com
    apply Proof.limpl
    . apply Proof.wek [A] p
    . change [] ++ [Q] ++ [] ++ [A] ++ X ⊢ B
      apply Proof.com
      apply rimpl_inv q
  | @Proof.lconjr Q X _ P p => by 
    have : Proof_size p < Proof_size (@Proof.lconjr Q X (A → B) P p) := by
      simp [Proof_size]
    change [] ++ [A] ++ [] ++ [P ∧ Q] ++ X ⊢ B
    apply Proof.com
    apply Proof.lconjr
    change [] ++ [Q] ++ [] ++ [A] ++ X ⊢ B
    apply Proof.com
    apply rimpl_inv p
  | @Proof.lconjl P X _ Q p => by 
    have : Proof_size p < Proof_size (@Proof.lconjl P X (A → B) P p) := by
      simp [Proof_size]
    change [] ++ [A] ++ [] ++ [P ∧ Q] ++ X ⊢ B
    apply Proof.com
    apply Proof.lconjl
    change [] ++ [P] ++ [] ++ [A] ++ X ⊢ B
    apply Proof.com
    apply rimpl_inv p  
  | @Proof.ldisj P X _ Q p q => by
    change [] ++ [A] ++ [] ++ [P ∨ Q] ++ X ⊢ B
    apply Proof.com
    apply Proof.ldisj
    . have : Proof_size p < Proof_size (Proof.ldisj p q) := by
        simp [Proof_size]
        linarith
      change [] ++ [P] ++ [] ++ [A] ++ X ⊢ B 
      apply Proof.com
      apply rimpl_inv p  
    . have : Proof_size q < Proof_size (Proof.ldisj p q) := by
        simp [Proof_size]
        linarith
      change [] ++ [Q] ++ [] ++ [A] ++ X ⊢ B 
      apply Proof.com
      apply rimpl_inv q 
  | @Proof.cut V C W _ p q => by
    have : Proof_size q < Proof_size (Proof.cut p q) := by
      simp [Proof_size]
      linarith
    change [] ++ [A] ++ [] ++ V ++ W ⊢ B
    apply Proof.com
    simp [List.append_assoc]
    apply Proof.cut (A := C)
    . assumption
    . apply Proof.com (X := []) (Y := []) (Z := W) (Γ := [A]) (Δ := [C])
      apply rimpl_inv q 
termination_by rimpl_inv p => Proof_size p  

def rconj_inv {Γ : List PropForm} {A B : PropForm} : (Γ ⊢ A ∧ B) → ((Γ ⊢ A) × (Γ ⊢ B))
  | Proof.id => (Proof.lconjl (@Proof.id A), Proof.lconjr (@Proof.id B))
  | Proof.exfal => (@Proof.exfal A, @Proof.exfal B)
  | Proof.com Γ Δ D => (Proof.com Γ Δ (rconj_inv D).1, Proof.com Γ Δ (rconj_inv D).2)
  | Proof.wek X D => (Proof.wek X (rconj_inv D).1, Proof.wek X (rconj_inv D).2)
  | Proof.contr X D => (Proof.contr X (rconj_inv D).1, Proof.contr X (rconj_inv D).2)
  | Proof.limpl D E => (Proof.limpl D (rconj_inv E).1, (Proof.limpl D (rconj_inv E).2))
  | Proof.rconj D E=> (D, E)
  | Proof.lconjr D => (Proof.lconjr (rconj_inv D).1, Proof.lconjr (rconj_inv D).2)
  | Proof.lconjl D => (Proof.lconjl (rconj_inv D).1, Proof.lconjl (rconj_inv D).2)
  | Proof.ldisj D E => (Proof.ldisj (rconj_inv D).1 (rconj_inv E).1, (Proof.ldisj (rconj_inv D).2 (rconj_inv E).2))
  | Proof.cut D E => (Proof.cut D (rconj_inv E).1, (Proof.cut D (rconj_inv E).2))            

def ldisj_inv {Γ : List PropForm} {A B C: PropForm} : ((A ∨ B) :: Γ ⊢ C) → ((A :: Γ ⊢ C) × (B :: Γ ⊢ C)) := by  
  intro h
  generalize ih : (A ∨ B) :: Γ = Δ 
  --Need to generalize the assumption to avoid dependent elimination issue.
  rw [ih] at h
  cases h
  . have single : (A ∨ B) = C := by 
      apply List.head_eq_of_cons_eq ih
    rw [← single]
    constructor 
    . have deq : A :: Γ = [] ++ [A] ++ [] ++ Γ ++ [] := by simp
      rw [deq]
      apply Proof.com
      simp
      apply Proof.wek Γ (Proof.rdisjl (@Proof.id A))
    . have deq : B :: Γ = [] ++ [B] ++ [] ++ Γ ++ [] := by simp
      rw [deq]
      apply Proof.com
      simp
      apply Proof.wek Γ (Proof.rdisjr (@Proof.id B))
  . have := List.head_eq_of_cons_eq ih
    contradiction
    --Contradiction seems to work for impossibility from definition
  . rename_i X Y Z W V p  
    rw [List.cons_eq_append] at ih
    sorry
  . rename_i X Y p
    rw [List.cons_eq_append] at ih
    sorry
  . rename_i X Y p 
    rw [List.cons_eq_append] at ih
    sorry 
  . rename_i P Q p
    rw [← ih] at p
    have iih := ldisj_inv (@Proof.com [] [] Γ Q [P] [A ∨ B] p)
    simp [List] at iih 
    apply (Proof.rimpl (@Proof.com [] [] Γ Q [A] [P] (iih.1)), Proof.rimpl (@Proof.com [] [] Γ Q [B] [P] (iih.2)))
  . have := List.head_eq_of_cons_eq ih 
    contradiction
    --Nice!
  . rename_i P Q p q 
    rw [← ih] at p 
    rw [← ih] at q
    apply (Proof.rconj (ldisj_inv p).1  (ldisj_inv q).1, Proof.rconj (ldisj_inv p).2 (ldisj_inv q).2) 
  . have := List.head_eq_of_cons_eq ih 
    contradiction
  . have := List.head_eq_of_cons_eq ih 
    contradiction
  . rename_i P Q p
    rw [← ih] at p 
    apply (@Proof.rdisjl (A :: Γ) P Q (ldisj_inv p).1, @Proof.rdisjl (B :: Γ) P Q (ldisj_inv p).2)
  . rename_i P Q p
    rw [← ih] at p 
    apply (@Proof.rdisjr (A :: Γ) P Q (ldisj_inv p).1, @Proof.rdisjr (B :: Γ) P Q (ldisj_inv p).2)
  . rename_i P X Q p q 
    have ih1 := List.head_eq_of_cons_eq ih 
    have ih2 := List.tail_eq_of_cons_eq ih 
    injection ih1 with ih11 ih12
    rw [ih2, ih11, ih12] 
    apply (p,q)
  . rename_i X P Y p q 
    sorry 
  




