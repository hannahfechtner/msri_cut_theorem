import MyProject.Definitions
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

theorem CF_Regular {Γ : List PropForm} {A : PropForm} : (Γ ⊢₁ A) → (Γ ⊢ A) := by 
  intro h
  induction h
  . exact Proof.id 
  . exact Proof.exfal
  . rename_i ih
    apply Proof.com
    exact ih 
  . rename_i ih
    apply Proof.wek
    exact ih
  . rename_i ih
    apply Proof.contr
    exact ih
  . rename_i ih
    apply Proof.rimpl
    exact ih
  . rename_i ih1 ih2
    apply Proof.limpl
    . exact ih1 
    exact ih2
  . rename_i ih1 ih2
    apply Proof.rconj
    . exact ih1
    exact ih2
  . rename_i ih
    apply Proof.lconjl
    exact ih
  . rename_i ih
    apply Proof.lconjr
    exact ih
  . rename_i ih
    apply Proof.rdisjl
    exact ih
  . rename_i ih
    apply Proof.rdisjr
    exact ih
  . rename_i ih1 ih2
    apply Proof.ldisj
    . exact ih1
    exact ih2
  

