import MyProject.Definitions
open sequent_calculus

theorem EX_more {Γ : List PropForm} {A : PropForm} : ⊥ :: Γ ⊢₁ A := by sorry

  

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
  

