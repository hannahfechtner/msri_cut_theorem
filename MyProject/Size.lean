import MyProject.Definitions

--Define maximum cut depth of a given proof tree.

def Depth_Cut {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ
  | Proof.id => 0 
  | Proof.exfal => 0
  | Proof.com _ _ D => Depth_Cut D
  | Proof.wek _ D => Depth_Cut D
  | Proof.contr _ D => Depth_Cut D
  | Proof.rimpl D => Depth_Cut D
  | Proof.limpl D E => max (Depth_Cut D) (Depth_Cut E)
  | Proof.rconj D E => max (Depth_Cut D) (Depth_Cut E)
  | Proof.lconjl D => Depth_Cut D
  | Proof.lconjr D => Depth_Cut D
  | Proof.rdisjl D => Depth_Cut D
  | Proof.rdisjr D => Depth_Cut D
  | Proof.ldisj D E => max (Depth_Cut D) (Depth_Cut E)
  | Proof.cut D E => max (Depth_Cut D) (Depth_Cut E) + 1

--Define the sum of complexities of all cut formulas

def Size_Cut {Γ : List PropForm} {A : PropForm} : Proof Γ A →  ℕ
  | Proof.id => 0 
  | Proof.exfal => 0
  | Proof.com _ _ D => Size_Cut D 
  | Proof.wek _ D => Size_Cut D
  | Proof.contr _ D => Size_Cut D
  | Proof.rimpl D => Size_Cut D
  | Proof.limpl D E => Size_Cut D + Size_Cut E
  | Proof.rconj D E => Size_Cut D + Size_Cut E
  | Proof.lconjl D => Size_Cut D
  | Proof.lconjr D => Size_Cut D
  | Proof.rdisjl D => Size_Cut D 
  | Proof.rdisjr D => Size_Cut D
  | Proof.ldisj D E => Size_Cut D + Size_Cut E + 1 
  | @Proof.cut _ A _ D E => Size_Cut D + Size_Cut E + Complexity A

--A measure to allow recursion on proof trees.

def Data_Cut {Γ : List PropForm} {A : PropForm} (D : Proof Γ A) : ℕ × ℕ := ⟨Depth_Cut D, Size_Cut D⟩ 