import MyProject.Definitions

open sequent_calculus

theorem transport_CF {Γ Δ : List PropForm} {A : PropForm} : (Γ ++ Δ  ⊢₁ A) → (Δ ++ Γ ⊢₁ A)  := by
  intro h
  have this : [] ++ Δ  ++ [] ++ Γ  ++ [] = Δ  ++ Γ := by
    simp
  rw [← this]
  apply Proof_CF.com
  simp
  assumption

theorem modus_ponens {A B : PropForm} : [A, A → B] ⊢ B := 
@Proof.com [] [] [] _ [_] [_] (Proof.limpl (@Proof.id A) (@Proof.com [] [] [] _ [_] [_] (Proof.wek [A] (@Proof.id B))))

theorem disjunctive_syllogism : [&0 ∨ &1, ¬ &0] ⊢ &1 := by
  apply Proof.ldisj
  . apply @Proof.com [] [] [] _ [_] [_] 
    apply Proof.limpl
    . apply Proof.id
    . apply @Proof.com [] [] [] _ [_] [_] 
      apply Proof.wek [&0]
      apply Proof.exfal
  . apply @Proof.com [] [] [] _ [_] [_] 
    apply Proof.wek [¬ &0]
    apply Proof.id
    
theorem distributivity: [] ⊢ &0 ∨ &1 ∧ &2 ↔ (&0 ∨ &1) ∧ (&0 ∨ &2) := by 
  apply Proof.rconj
  . apply Proof.rimpl
    sorry
  . apply Proof.rimpl
    apply Proof.contr [( & 0 ∨ & 1) ∧ ( & 0 ∨ & 2)]
    apply Proof.lconjl
    apply @Proof.com [] [] [] _ [_] [_] 
    apply Proof.lconjr
    apply Proof.ldisj 
    . apply Proof.rdisjl 
      apply @Proof.com [] [] [] _ [_] [_] 
      apply Proof.wek [& 0 ∨ & 1]
      apply Proof.id
    . apply @Proof.com [] [] [] _ [_] [_] 
      apply Proof.ldisj
      . apply Proof.rdisjl
        apply @Proof.com [] [] [] _ [_] [_] 
        apply Proof.wek [&2]
        apply Proof.id
      . apply Proof.rdisjr 
        apply Proof.rconj
        . apply @Proof.com [] [] [] _ [_] [_] 
          apply Proof.wek [&2]
          apply Proof.id
        . apply Proof.wek [&1]
          apply Proof.id
