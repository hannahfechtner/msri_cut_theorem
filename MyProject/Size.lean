import MyProject.Definitions

open sequent_calculus

--A measure to allow recursion on proof trees.

--Define maximum cut depth of a given proof tree.

def Proof_size {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ
  | Proof.id => 1
  | Proof.exfal => 1
  | Proof.com _ _ D => Proof_size D +1
  | Proof.wek _ D => Proof_size D +1
  | Proof.contr _ D => Proof_size D +1
  | Proof.rimpl D => Proof_size D +1
  | Proof.limpl D E =>  (Proof_size D) + (Proof_size E) +1
  | Proof.rconj D E =>  (Proof_size D) + (Proof_size E) +1
  | Proof.lconjl D => Proof_size D +1
  | Proof.lconjr D => Proof_size D +1
  | Proof.rdisjl D => Proof_size D +1
  | Proof.rdisjr D => Proof_size D +1
  | Proof.ldisj D E =>  (Proof_size D) + (Proof_size E) +1
  | Proof.cut D E =>  (Proof_size D) + (Proof_size E) + 1


--A lemma dealing with definitional equality between proofs
def cast_same_size {Γ Δ : List PropForm} {A : PropForm} {p : Γ ⊢ A} (h : (Γ ⊢ A) = (Δ ⊢ A)) : Proof_size (cast h p) = Proof_size p := by
  sorry 

--may need to subtly change this format to show it's simulataneous on D and E
def Data_Cut {Γ₁ Γ₂  : List PropForm} {A C : PropForm} (D : Proof Γ₁ A) (E : Proof (A::Γ₂) C) : ℕ × ℕ × ℕ := (Complexity A, Proof_size D, Proof_size E) 


def less_than (A B : ℕ × ℕ) : Prop := 
  Or (A.1<B.1) (And (A.1=B.1)  (A.2 < B.1))

example : less_than (0,2) (1,1) := by 
  sorry
  -- left
  -- norm_num 

example : less_than (1,0) (1,1) := by 
  sorry
  -- right
  -- norm_num 

infix: 30 "≺" => less_than