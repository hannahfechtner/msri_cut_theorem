import MyProject.Definitions
import MyProject.Size

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
    . suffices : [] ++ [PropForm.fls] ++ [] ++ Γ₁ ++ [] ⊢₁ B
      · simpa using this
      . apply Proof_CF.com 
        simp
        apply Proof_CF.wek
        apply Proof_CF.exfal
      --have this : [] ++ [PropForm.fls] ++ [] ++ Γ₁ ++ [] = [PropForm.fls] ++ Γ₁ := by
        --simp
      --rw [← this]
      --apply @Proof.com [] [] [] B Γ₁ [PropForm.fls]
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
    
    -- here below is the bot case
  . cases' d
    . exact Proof_CF.contr g 
    . exact Proof_CF.exfal
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
    . exact Proof_CF.exfal
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
    . exact Proof_CF.contr g
    . exact Proof_CF.exfal
    . rename_i G X H Y I a
      apply hauptsatz (Proof.cut (Proof.com a) e)
    . rename_i G X a
      apply hauptsatz (Proof.cut (Proof.wek a) e)
    . rename_i X G a
      apply hauptsatz (Proof.cut (Proof.contr a) e)
    . rename_i G X Y a b 
      apply hauptsatz (Proof.cut (Proof.limpl a b) e) 
    . rename_i X Y
      apply hauptsatz 
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
  . rename_i CF₁ CF₂ h i
    cases' d
    . exact Proof_CF.contr g
    . exact Proof_CF.exfal
    . rename_i G X H Y I a
      apply hauptsatz (Proof.cut (Proof.com a) e)
    . rename_i G X a
      apply hauptsatz (Proof.cut (Proof.wek a) e)

    . rename_i X G a
      apply hauptsatz (Proof.cut (Proof.contr a) e)

    . rename_i G X Y a b 
      apply hauptsatz (Proof.cut (Proof.limpl a b) e)

    . rename_i X G Y a
      apply hauptsatz (Proof.cut (Proof.lconjl a) e)

    . rename_i X G Y a
      apply hauptsatz (Proof.cut (Proof.lconjr a) e)

    . rename_i a
      apply hauptsatz (Proof.cut (Proof.rdisjl a) e)
      
    . rename_i a
      apply hauptsatz (Proof.cut (Proof.rdisjr a) e)

    . rename_i X G Y a b
      apply hauptsatz (Proof.cut (Proof.ldisj a b) e)

    . rename_i X a b
      sorry
  termination_by hauptsatz A => Data_Cut A 