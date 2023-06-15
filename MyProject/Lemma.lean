import MyProject.Definitions
import MyProject.Properties
import MyProject.Size

theorem CF_Regular {Γ : List PropForm} {A : PropForm} : (Proof_CF Γ A) → (Proof Γ A) := by 
  rename_i one two 
  intro h
  induction h 
  . 