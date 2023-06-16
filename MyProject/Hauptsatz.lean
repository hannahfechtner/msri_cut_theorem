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
      apply Proof_CF.limpl
      . have thing : [] ++ G ++ [] ++ Γ₁ ++[] =  List.append G Γ₁ := by simp
        rw [← thing]
        apply Proof_CF.com 
        simp
        apply Proof_CF.wek
        exact hauptsatz a
      apply hauptsatz
      have thing: Y :: List.append G Γ₁= ([Y]++G) ++Γ₁ := by simp
      rw [thing]
      apply Proof.cut (A:= &N) 
      . apply b 
      apply e
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjl c) e)
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjr c) e) 
    . rename_i X Y a b c
      apply hauptsatz 
      apply (Proof.cut (Proof.ldisj b c) e)
    . rename_i Y a b
      apply hauptsatz 
      sorry
    
    -- here below is the bot case
  . cases' d
    . assumption
    . apply EX_more
    . rename_i G X H Y I a
      apply hauptsatz (Proof.cut (Proof.com a) e)
    . rename_i G X a
      apply hauptsatz (Proof.cut (Proof.wek a) e)
    . rename_i X G a
      apply hauptsatz (Proof.cut (Proof.contr a) e)
    . rename_i G X Y a b 
      apply hauptsatz (Proof.cut (Proof.limpl a b) e) 
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjl c) e)
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjr c) e) 
    . rename_i X Y a b c
      apply hauptsatz 
      apply (Proof.cut (Proof.ldisj b c) e)
    . rename_i Y a b
      apply hauptsatz 
      sorry
    -- here below is the impl case
  . rename_i CF₁ CF₂ h i
    cases' d
    . exact Proof_CF.contr g 
    . apply EX_more
    . rename_i G X H Y I a
      apply hauptsatz (Proof.cut (Proof.com a) e)
    . rename_i G X a
      apply hauptsatz (Proof.cut (Proof.wek a) e)
    . rename_i X G a
      apply hauptsatz (Proof.cut (Proof.contr a) e)
    . rename_i a
      apply hauptsatz (Proof.cut (Proof.rimpl a) e) 
    . rename_i  Y a b 
      apply hauptsatz (Proof.cut (Proof.limpl a b) e) 
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjl c) e)
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjr c) e) 
    . rename_i X Y a b c
      apply hauptsatz 
      apply (Proof.cut (Proof.ldisj b c) e)
    . rename_i Y a b
      apply hauptsatz 
      sorry
    -- here below is the conj case
  . rename_i CF₁ CF₂ h i
    cases' d
    . assumption
    . apply EX_more
    . rename_i G X H Y I a
      apply hauptsatz (Proof.cut (Proof.com a) e)
    . rename_i G X a
      apply hauptsatz (Proof.cut (Proof.wek a) e)
    . rename_i X G a
      apply hauptsatz (Proof.cut (Proof.contr a) e)
    . rename_i G X Y a b 
      apply hauptsatz (Proof.cut (Proof.limpl a b) e) 
    . rename_i X Y
      --revert e
      --generalize ((CF₁ ∧ CF₂) :: Γ₁ ⊢ B) = e
      --have thing: ((CF₁ ∧ CF₂) :: Γ₁) = List.append ([] ++ [CF₁ ∧ CF₂] ++ [] ++ Γ₁) [] := by simp
      --rw [thing] at e
      match e with
        | Proof.id => _
        | Proof.exfal => _
        | _ => sorry 
      sorry
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjl c) e) 
    . rename_i Z a Y c 
      apply hauptsatz 
      apply (Proof.cut (Proof.lconjr c) e) 
    . rename_i X Y a b c
      apply hauptsatz 
      apply (Proof.cut (Proof.ldisj b c) e)
    . rename_i Y a b
      apply hauptsatz 
      sorry

    --here below is the disj case
  . rename_i X Y a b 
    cases' d
    . sorry
    . sorry
    . sorry 
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
      
    . rename_i X a b
      sorry
  
  
  termination_by hauptsatz A => Data_Cut A 