import MyProject.Definitions

--Some examples.

theorem identity : [&0] ⊢ &0 := Proof.id 

theorem modus_ponens : [&0 → &1, &0] ⊢ &1 := by 
  apply Proof.limpl
  . apply Proof.id 
  . change [] ++ &1 :: [] ++ &0 :: [] ⊢ &1
    apply Proof.com 
    apply Proof.wek
    apply Proof.id

--More examples.

theorem disjunctive_syllogism : [&0 ∨ &1, ¬ &0] ⊢ &1 := by
  apply Proof.ldisj
  . change [] ++ &0 :: [] ++ (¬ &0) :: [] ⊢ &1
    apply Proof.com
    apply Proof.limpl
    . apply Proof.id
    . change [] ++ fls :: [] ++ &0 :: [] ⊢ &1
      apply Proof.com 
      apply Proof.wek
      apply Proof.exfal
  . change [] ++ &1 :: [] ++ (¬ &0) :: [] ⊢ &1
    apply Proof.com
    apply Proof.wek
    apply Proof.id

theorem distributivity: [] ⊢ &0 ∨ &1 ∧ &2 ↔ (&0 ∨ &1) ∧ (&0 ∨ &2) := by 
  apply Proof.rconj
  . apply Proof.rimpl
    sorry
  . apply Proof.rimpl
    apply Proof.contr
    apply Proof.lconjl
    change [] ++ (&0 ∨ &1) :: [] ++ ((&0 ∨ &1) ∧ (&0 ∨ &2)) :: _ ⊢ _
    apply Proof.com
    apply Proof.lconjr
    apply Proof.ldisj 
    . apply Proof.rdisjl 
      change [] ++ &0 :: [] ++ (&0 ∨ &1) :: _ ⊢ _
      apply Proof.com
      apply Proof.wek
      apply Proof.id
    . change [] ++ &2 :: [] ++ (&0 ∨ &1) :: _ ⊢ _
      apply Proof.com
      apply Proof.ldisj
      . apply Proof.rdisjl
        change [] ++ &0 :: [] ++ &2 :: _ ⊢ _
        apply Proof.com
        apply Proof.wek
        apply Proof.id
      . apply Proof.rdisjr 
        apply Proof.rconj
        . change [] ++ &1 :: [] ++ &2 :: _ ⊢ _
          apply Proof.com
          apply Proof.wek
          apply Proof.id
        . apply Proof.wek
          apply Proof.id     
