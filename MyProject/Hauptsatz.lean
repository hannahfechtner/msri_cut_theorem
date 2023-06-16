import MyProject.Definitions
import MyProject.Size
import MyProject.Lemma

open sequent_calculus

theorem hauptsatz {Γ : List PropForm} {A : PropForm} : (Γ ⊢ A) → (Γ ⊢₁ A) := by 
  intro h
  induction h 
  . apply Proof_CF.id 
  . apply Proof_CF.exfal
  . case com last => 
    apply Proof_CF.com 
    --rename_i last
    exact last
  . apply Proof_CF.wek
    rename_i last
    exact last
  . apply Proof_CF.contr
    rename_i last
    exact last
  . apply Proof_CF.rimpl
    rename_i last
    exact last 
  . next Γ A _ _ _ _ ih1 ih2 =>
    apply Proof_CF.limpl
    . exact ih1  
    exact ih2
  . apply Proof_CF.rconj
    . rename_i second_to last
      exact second_to
    rename_i last
    exact last
  . apply Proof_CF.lconjl
    rename_i last
    exact last
  . apply Proof_CF.lconjr
    rename_i last
    exact last
  . apply Proof_CF.rdisjl
    rename_i last
    exact last
  . apply Proof_CF.rdisjr
    rename_i last
    exact last
  . apply Proof_CF.ldisj
    . rename_i second_to last
      exact second_to
    rename_i last
    exact last
  -- here's the big one!
  
  rename_i Γ₀ CF Γ₁ B d e f g
  induction CF
    -- here below is the Var case
  . rename_i N
    cases' d
    . assumption
    . apply EX_more 
    . rename_i X Y Z W V d 
      have deq : X ++ V ++ Y ++ W ++ (Z ++ Γ₁) = X ++ V ++ Y ++ W ++ Z ++ Γ₁ := by
        simp  
      rw [← deq]
      apply @Proof_CF.com
      simp
      have := hauptsatz (Proof.cut d e)
      simp at this 
      assumption
    . rename_i G X a
      have deq : X ++ G ++ Γ₁ = X ++ (G ++ Γ₁) := by
        simp
      rw [deq] 
      apply Proof_CF.wek
      apply hauptsatz (Proof.cut a e)
    . rename_i X G a
      have deq : G ++ X ++ Γ₁ = G ++ (X ++ Γ₁) := by
        simp
      rw [deq] 
      apply Proof_CF.contr
      simp 
      have := hauptsatz (Proof.cut a e)
      simp at this
      assumption
    . rename_i G X Y a b 
      apply Proof_CF.limpl (transport_CF (Proof_CF.wek Γ₁ (hauptsatz a))) (hauptsatz (Proof.cut b e))
    . rename_i Z a Y c 
      exact Proof_CF.lconjl (hauptsatz (Proof.cut c e))
    . rename_i Z a Y c 
      exact Proof_CF.lconjr (hauptsatz (Proof.cut c e))
    . rename_i X Y a b c
      exact Proof_CF.ldisj (hauptsatz (Proof.cut b e) ) (hauptsatz (Proof.cut c e))
    . rename_i X Y a b c
      apply hauptsatz 
      apply @Proof.cut _ (&N)
      . apply CF_C (hauptsatz (Proof.cut b c))
      . apply CF_C (hauptsatz e)
    
    -- here below is the bot case
  . cases' d
    . assumption
    . apply EX_more
    . rename_i G X H Y I a
      have d: G ++ I ++ X ++ Y ++ H ++ Γ₁ = G ++ I ++ X ++ Y ++ (H ++ Γ₁) := by simp
      rw [d]
      apply Proof_CF.com
      have d': G ++ Y ++ X ++ I ++ (H ++ Γ₁) = G ++ Y ++ X ++ I ++ H ++ Γ₁ := by simp
      rw [d']
      exact hauptsatz (Proof.cut a e)
    . rename_i G X a
      have d : X ++ G ++ Γ₁ = X ++ (G ++ Γ₁) := by simp 
      rw [d]
      exact Proof_CF.wek X (hauptsatz (Proof.cut a e))
    . rename_i X G a
      have d : G ++ X ++ Γ₁ = G ++ (X ++ Γ₁) := by simp
      rw [d]
      apply Proof_CF.contr G
      have d' : G ++ G ++ X ++ Γ₁ = G ++ G ++ (X ++ Γ₁) := by simp
      rw [← d'] 
      exact hauptsatz (Proof.cut a e)
    . rename_i G X Y a b 
      apply Proof_CF.limpl (transport_CF (Proof_CF.wek Γ₁ (hauptsatz a))) (hauptsatz (Proof.cut b e))
    . rename_i Z a Y c 
      exact Proof_CF.lconjl (hauptsatz (Proof.cut c e))
    . rename_i Z a Y c 
      exact Proof_CF.lconjr (hauptsatz (Proof.cut c e))
    . rename_i X Y a b c
      exact Proof_CF.ldisj (hauptsatz (Proof.cut b e) ) (hauptsatz (Proof.cut c e))
    . rename_i X a Y b c  
      apply hauptsatz 
      have deq : (X ++ Y) ++ Γ₁ = X ++ Y ++ Γ₁ := by simp
      rw [← deq]
      apply @Proof.cut _ PropForm.fls
      . apply CF_C (hauptsatz (Proof.cut b c))
      . apply CF_C (hauptsatz e)

    -- here below is the impl case
  . rename_i CF₁ CF₂ h i
    generalize h' : (CF₁ → CF₂) :: Γ₁ = Δ 
    rw [h'] at e
    cases' e
    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d
    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 

    . rename_i one two three
      apply Proof_CF.rimpl
      apply hauptsatz
      have thing : one :: (Γ₀++Γ₁) = [] ++ [one] ++ [] ++ Γ₀ ++ Γ₁ := by simp
      rw [thing]
      apply Proof.com
      simp
      apply Proof.cut (A := (CF₁ →CF₂))
      . exact d
      rw [← h'] at three
      have that : (CF₁ → CF₂) :: one :: Γ₁ = [] ++ [(CF₁ → CF₂)] ++ [] ++ [one] ++ Γ₁ := by simp 
      rw [that]
      apply Proof.com
      simp
      exact three
    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 

    . apply Proof_CF.rconj
      rename_i X Y x y
      . apply hauptsatz
        have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
        rw [that]
        apply Proof.com
        simp
        have thing : (CF₁ → CF₂) = X := by sorry
        rw [← thing]
        apply Proof.wek
        exact d
        
        

      rename_i X Y x y
      . apply hauptsatz
        have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
        rw [that]
        apply Proof.com
        simp
        have thing : (CF₁ → CF₂) = Y := by sorry
        rw [← thing]
        apply Proof.wek
        exact d

     

    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 

    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 

    . apply Proof_CF.rdisjl
      rename_i Y X y
      apply hauptsatz
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof.com
      simp
      have thing : (CF₁ → CF₂) = Y := by sorry
      rw [← thing]
      apply Proof.wek
      exact d


    . apply Proof_CF.rdisjl
      rename_i Y X y
      apply hauptsatz
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof.com
      simp
      have thing : (CF₁ → CF₂) = X := by sorry
      rw [← thing]
      apply Proof.wek
      exact d


    . revert h'
      intro ih
      have thing : (CF₁ → CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . sorry


    -- here below is the conj case
  . rename_i CF₁ CF₂ h i
    generalize h' : (CF₁ ∧ CF₂) :: Γ₁ = Δ 
    rw [h'] at e
    cases' e
    . revert h'
      intro ih
      have thing : (CF₁ ∧ CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d
    . revert h'
      intro ih
      have thing : (CF₁ ∧ CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . revert h'
      intro ih
      have thing : (CF₁ ∧ CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . revert h'
      intro ih
      have thing : (CF₁ ∧ CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . revert h'
      intro ih
      have thing : (CF₁ ∧ CF₂) = B := by sorry
      rw [← thing]
      have that : (Γ₀ ++ Γ₁) = ([] ++ Γ₀ ++ [] ++ Γ₁ ++ []) := by simp
      rw [that]
      apply Proof_CF.com
      simp
      apply Proof_CF.wek
      apply hauptsatz
      exact d 
    . apply Proof_CF.rimpl
      apply hauptsatz
      rename_i one two three
      have thing : [] ++ [one] ++[] ++ Γ₀ ++Γ₁  = one :: (Γ₀ ++ Γ₁) := by simp
      rw [← thing]
      apply Proof.com
      simp
      apply Proof.cut (A:= (CF₁ ∧ CF₂))
      . exact d
      rw [← h'] at three 
      have that : (CF₁ ∧ CF₂) :: one :: Γ₁ = [] ++ [(CF₁ ∧ CF₂)] ++ [] ++ [one] ++Γ₁ := by simp
      rw [that]
      apply Proof.com
      simp
      exact three
    . rename_i one two three four five
      sorry
    . rename_i D E Y c 
      apply Proof_CF.rconj
      . apply hauptsatz
        apply Proof.cut (A:= CF₁ ∧ CF₂)
        . exact d
        rw [h']
        exact Y
      apply hauptsatz
      apply Proof.cut (A:= CF₁ ∧ CF₂)
      . exact d
      rw [h']
      exact c
    . rename_i Z a Y c 
      apply hauptsatz
      apply Proof.cut (A := CF₁)
      . exact (rconj_inv d).1
      have this : (Γ₁ = a) := by sorry
      have that : (CF₁ ∧ CF₂) = (Z ∧ Y) := by sorry
      rw [this]
      have last : CF₁=Z := by sorry
      rw [last]
      exact c
    . rename_i Z a Y c
      apply hauptsatz
      apply Proof.cut (A := CF₂)
      . exact (rconj_inv d).2
      have this : (Γ₁ = a) := by sorry
      have that : (CF₁ ∧ CF₂) = (Y ∧ Z) := by sorry
      rw [this]
      have last : CF₂=Z := by sorry
      rw [last]
      exact c
    . rename_i D E b
      apply Proof_CF.rdisjl
      apply hauptsatz
      apply Proof.cut (A:= CF₁ ∧ CF₂)
      . exact d
      rw [h']
      exact b
    sorry
    sorry
    sorry

    --here below is the disj case
  . rename_i X Y a b 
    cases' d
    . apply hauptsatz e

    . apply transport_CF
      apply Proof_CF.wek Γ₁  
      apply Proof_CF.exfal

    . rename_i Θ Λ Ξ Γ Δ x
      have d: Θ ++ Δ ++ Λ ++ Γ ++ Ξ ++ Γ₁ = Θ ++ Δ ++ Λ ++ Γ ++ (Ξ ++ Γ₁) := by simp
      rw [d]
      apply Proof_CF.com
      have d': Θ ++ Γ ++ Λ ++ Δ ++ (Ξ ++ Γ₁) = Θ ++ Γ ++ Λ ++ Δ ++ Ξ ++ Γ₁ := by simp
      rw [d']
      exact hauptsatz (Proof.cut x e)

    . rename_i Γ Δ x 
      have d : Δ ++ Γ ++ Γ₁ = Δ ++ (Γ ++ Γ₁) := by simp 
      rw [d]
      exact Proof_CF.wek Δ (hauptsatz (Proof.cut x e))
    . rename_i Γ Δ x 
      have d : Δ ++ Γ ++ Γ₁ = Δ ++ (Γ ++ Γ₁) := by simp
      rw [d]
      apply Proof_CF.contr Δ
      have d' : Δ ++ Δ ++ Γ ++ Γ₁ = Δ ++ Δ ++ (Γ ++ Γ₁) := by simp
      rw [← d'] 
      exact hauptsatz (Proof.cut x e)

    . rename_i Γ G H x y 
      apply Proof_CF.limpl (transport_CF (Proof_CF.wek Γ₁ (hauptsatz x))) (hauptsatz (Proof.cut y e))
      
    . rename_i G Γ H x 
      exact Proof_CF.lconjl (hauptsatz (Proof.cut x e))

    . rename_i G Γ H x 
      exact Proof_CF.lconjr (hauptsatz (Proof.cut x e))

    . rename_i x
      have thing := (ldisj_inv e).1
      have other := Proof.cut x thing 
      exact (hauptsatz other)
    . rename_i x
      have thing := (ldisj_inv e).2
      have other := Proof.cut x thing 
      exact (hauptsatz other)
    . rename_i G Γ H x y
      exact Proof_CF.ldisj (hauptsatz (Proof.cut x e) ) (hauptsatz (Proof.cut y e))
    . rename_i m n o p q
      apply hauptsatz
      have deq : (m ++ o) ++ Γ₁ = m ++ o ++ Γ₁ := by 
        simp
      rw [← deq]
      apply @Proof.cut _ (X ∨ Y)
      . apply CF_C (hauptsatz (Proof.cut p q))
      . apply CF_C (hauptsatz e)

  termination_by hauptsatz A => Proof_size A 
