import MyProject.Definitions
import MyProject.Properties
import MyProject.Size

theorem CF_Regular {Γ : List PropForm} {A : PropForm} : (Γ ⊢₁ A) → (Γ ⊢ A) := by 
  intro h
  induction h 
  . 