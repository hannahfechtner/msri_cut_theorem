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
    have : Proof_size p < Proof_size (Proof.contr X p) := by 
      simp [Proof_size]
    change [] ++ [A] ++ [] ++ X ++ Y ⊢ B
    apply Proof.com
    rw [List.append_assoc, List.nil_append, List.append_nil]
    apply Proof.contr X
    rw [← List.append_assoc, ← List.nil_append (X ++ X), ← List.append_nil ([] ++ (X ++ X))]
    apply Proof.com 
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

def lconj_inv {Γ : List PropForm} {A B C: PropForm} : ((A ∧ B) :: Γ ⊢ C) → (A :: B :: Γ ⊢ C) := by
  sorry
  -- intro h
  -- generalize ih : (A ∧ B) :: Γ = Δ 
  -- rw [ih] at h
  -- cases h
  -- . injection ih with ih1 ih2
  --   rw [ih2, ← ih1]  
  --   change [] ++ [A] ++ [] ++ [B] ++ [] ⊢ A ∧ B
  --   apply  Proof.rconj (@Proof.com [] [] [] _ [_] [_] (Proof.wek [B] (@Proof.id A))) (Proof.wek [A] (@Proof.id B))
  -- . injection ih
  --   contradiction
  -- . sorry
  -- . sorry
  -- . sorry
  -- . sorry
  -- . injection ih 
  --   contradiction
  -- . sorry
  -- . sorry
  -- . sorry
  -- . sorry
  -- . sorry 
  -- . injection ih 
  --   contradiction
  -- . sorry

def ldisj_inv {Γ : List PropForm} {A B C: PropForm} : ((A ∨ B) :: Γ ⊢ C) → ((A :: Γ ⊢ C) × (B :: Γ ⊢ C)) := by  
  sorry
--   intro h
--   generalize ih : (A ∨ B) :: Γ = Δ
--   rw [ih] at h
--   cases h 
--   . injection ih with ihd iht
--     rw [← ihd, iht]
--     apply (Proof.rdisjl B (Proof.id A), Proof.rdisjr A (Proof.id B))
--   . injection ih
--     contradiction
--   . rename_i X Y Z P Q p 
--     cases X 
--     . injection ih with ihh iht
--       rw [← ihh] at p
--       rw [iht]
--       apply ldisj_inv (Proof.com P (A ∨ B) p)
--     . rename_i R U
--       injection ih with ihh iht
--       rw [← ihh] at p
--       rw [iht]
--       have := (ldisj_inv p).1
--       sorry
--     -- It is almost done but I realize I need a further lemma for Proof.com case.
--   . rename_i X P p 
--     injection ih with ihh iht
--     rw [← iht] at p 
--     apply (Proof.wek A p, Proof.wek B p) 
--   . rename_i P X p
--     injection ih with ihh iht
--     rw [← iht, ← ihh] at p 
--     apply (Proof.contr (ldisj_inv (@Proof.com [] [] Γ _ A (A ∨ B) (ldisj_inv p).1)).1, 
--     Proof.contr (ldisj_inv (@Proof.com [] [] Γ _ B (A ∨ B) (ldisj_inv p).2)).2)
--   . rename_i P Q p
--     rw [← ih] at p
--     have iih := ldisj_inv (@Proof.com [] [] Γ _ P (A ∨ B) p)
--     apply (Proof.rimpl (@Proof.com [] [] Γ _ A P (iih.1)), 
--     Proof.rimpl (@Proof.com [] [] Γ _ B P (iih.2)))
--   . injection ih
--     contradiction
--   . rename_i P Q p q
--     rw [← ih] at p q
--     apply (Proof.rconj (ldisj_inv p).1 (ldisj_inv q).1
--     , Proof.rconj (ldisj_inv p).2 (ldisj_inv q).2)
--   . injection ih
--     contradiction
--   . injection ih
--     contradiction
--   . rename_i P Q p 
--     rw [← ih] at p 
--     apply (Proof.rdisjl Q (ldisj_inv p).1, Proof.rdisjl Q (ldisj_inv p).2)
--   . rename_i Q P p 
--     rw [← ih] at p 
--     apply (Proof.rdisjr P (ldisj_inv p).1, Proof.rdisjr P (ldisj_inv p).2)
--   . rename_i P X Q p q
--     injection ih with ihh iht
--     injection ihh with ihh1 ihh2
--     rw [← ihh1, ← iht] at p
--     rw [← ihh2, ← iht] at q
--     apply (p, q)
--   . rename_i P p q
--     rw [← ih] at p q
--     apply (Proof.cut (ldisj_inv p).1 (@Proof.com [] [] Γ _ A P (ldisj_inv (@Proof.com [] [] Γ _ P (A ∨ B) q)).1),
--     Proof.cut (ldisj_inv p).2 (@Proof.com [] [] Γ _ B P (ldisj_inv (@Proof.com [] [] Γ _ P (A ∨ B) q)).2))
-- termination_by ldisj_inv p => Proof_size p  
