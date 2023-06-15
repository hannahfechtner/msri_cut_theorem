import Mathlib.Data.Real.Basic
--secret message hehehe

--secret message hehehe

namespace sequent_calculus

--Redefine the type of propositons since Prop is not inductively defined.

inductive PropForm : Type where
  | var : ℕ → PropForm 
--| var : String → PropForm
  | fls
  | impl : PropForm → PropForm → PropForm
  | conj : PropForm → PropForm → PropForm
  | disj : PropForm → PropForm → PropForm

open PropForm

--Define complexity inductively for propositons.

def Complexity : PropForm → ℕ 
  | var _ => 0
  | fls => 0 
  | impl P Q => max (Complexity P) (Complexity Q) + 1
  | conj P Q => max (Complexity P) (Complexity Q) + 1
  | disj P Q => max (Complexity P) (Complexity Q) + 1

--In particular, atomic propositions are those of complexity 0.

def Atomic (P : PropForm) : Prop := Complexity P = 0 

--Create local notations for logic symbols.

prefix: 90 " & " => var 

notation: 70 " ⊥ " => fls

prefix: 80 " ¬ " => fun (A : PropForm) => impl A fls

infixl: 51 " →  " => impl

infixl: 53 " ∧ " => conj

infixl: 52 " ∨ " => disj

infixl: 50 " ↔ " => fun (A B : PropForm) => conj (impl A B) (impl B A)

example : Complexity (¬ ((&0 ∧ &1) → &0)) = 3 := by trivial      

--Define proof tree of a given sequent Γ ⊢ A inductively, using sequnent calculus.

inductive Proof : List PropForm → PropForm → Type where
  | id : Proof [A] A
  | exfal : Proof [⊥] A
  | com (Γ Δ : List PropForm) : Proof (Θ ++ Γ ++ Λ ++ Δ ++ Ξ) C → Proof (Θ ++ Δ ++ Λ ++ Γ ++ Ξ) C 
  | wek (Δ : List PropForm) : Proof Γ A → Proof (Δ ++ Γ) A
  | contr (Δ : List PropForm) : Proof (Δ ++ Δ ++ Γ) B → Proof (Δ ++ Γ) B
  | rimpl : Proof (A :: Γ) B → Proof Γ (A → B)
  | limpl : Proof Γ A →  Proof (B :: Γ) C  → Proof ((A → B) :: Γ) C
  | rconj : Proof Γ A → Proof Γ B → Proof Γ (A ∧ B)
  | lconjl : Proof (A :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | lconjr : Proof (B :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | rdisjl : Proof Γ A  → Proof Γ (A ∨ B)
  | rdisjr : Proof Γ B  → Proof Γ (A ∨ B)
  | ldisj : Proof (A :: Γ) C  → Proof (B :: Γ) C → Proof ((A ∨ B) :: Γ) C 
  | cut : Proof Γ₀ A →  Proof (A :: Γ₁) B → Proof (Γ₀ ++ Γ₁) B 

inductive Proof_CF : List PropForm → PropForm → Type where
  | id : Proof_CF [A] A
  | exfal : Proof_CF [⊥] A
  | com (Γ Δ : List PropForm) : Proof_CF (Θ ++ Γ ++ Λ ++ Δ ++ Ξ) C → Proof_CF (Θ ++ Δ ++ Λ ++ Γ ++ Ξ) C 
  | wek (Δ : List PropForm) : Proof_CF Γ A → Proof_CF (Δ ++ Γ) A
  | contr (Δ : List PropForm) : Proof_CF (Δ ++ Δ ++ Γ) B → Proof_CF (Δ ++ Γ) B
  | rimpl : Proof_CF (A :: Γ) B → Proof_CF Γ (A → B)
  | limpl : Proof_CF Γ A →  Proof_CF (B :: Γ) C  → Proof_CF ((A → B) :: Γ) C
  | rconj : Proof_CF Γ A → Proof_CF Γ B → Proof_CF Γ (A ∧ B)
  | lconjl : Proof_CF (A :: Γ) C  → Proof_CF ((A ∧ B) :: Γ) C
  | lconjr : Proof_CF (B :: Γ) C  → Proof_CF ((A ∧ B) :: Γ) C
  | rdisjl : Proof_CF Γ A  → Proof_CF Γ (A ∨ B)
  | rdisjr : Proof_CF Γ B  → Proof_CF Γ (A ∨ B)
  | ldisj : Proof_CF (A :: Γ) C  → Proof_CF (B :: Γ) C → Proof_CF ((A ∨ B) :: Γ) C 

--local notation for valid sequents

infixl: 40 " ⊢ " => Proof

infixl: 40 " ⊢₁ " => Proof_CF

--Define maximum cut depth of a given proof tree.

def Depth_Cut {Γ : List PropForm} {A : PropForm} : Proof Γ A →  ℕ
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
  | @Proof.cut _ A _ _ D E => Size_Cut D + Size_Cut E + Complexity A

--A measure to allow recursion on proof trees.

-- def Data_Cut {Γ : List PropForm} {A : PropForm} (D : Proof Γ A) : ℕ × ℕ := ⟨Depth_Cut D, Size_Cut D⟩ 
--Canonical embedding from Proof_CF to Proof.

-- def CF_to_C {Γ : List PropForm} {A : PropForm} : Proof_CF → Proof 
  --| Proof_CF.id => Proof.id 
  --sorry
  --done