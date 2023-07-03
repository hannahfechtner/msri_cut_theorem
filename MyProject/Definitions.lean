import Mathlib.Data.Real.Basic

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
  deriving Repr, DecidableEq

open PropForm

def PropForm.neg (A : PropForm) : PropForm := impl A fls

def PropForm.equiv (A B : PropForm) : PropForm := conj (impl A B) (impl B A)

--Define complexity inductively for propositons.

def Complexity : PropForm → ℕ 
  | var _ => 0
  | fls => 0
  | impl P Q =>  (Complexity P) + (Complexity Q) + 1
  | conj P Q =>  (Complexity P) + (Complexity Q) + 1
  | disj P Q =>  (Complexity P) + (Complexity Q) + 1
--In particular, atomic propositions are those of complexity 0.

def Atomic (P : PropForm) : Prop := Complexity P = 0 

--Create local notations for logic symbols.

prefix: 90 " & " => var 

notation: 70 " ⊥ " => fls

prefix: 80 " ¬ " => neg

infixl: 51 " →  " => impl

infixl: 53 " ∧ " => conj

infixl: 52 " ∨ " => disj

infixl: 50 " ↔ " => equiv

-- #eval Complexity (¬ ((&0 ∧ &1) → &0))  

--Define proof tree of a given sequent Γ ⊢ A inductively, using sequent calculus.

inductive Proof : List PropForm → PropForm → Type where
  --The choice of list is not the most pleasant thing but it seems to be the best option so far.
  --Tried Multiset, which causes dependent elimination problem for any cases on proofs.
  | id : Proof [A] A
  --We use simpler axioms and add weakening as an inference rule.
  --It is both for aesthetic reason and possible expedition to substructural logics in the future. 
  | exfal : Proof [⊥] A
  | com (Γ Δ : List PropForm) : Proof (X ++ Γ ++ Y ++ Δ ++ Z) C → Proof (X ++ Δ ++ Y ++ Γ ++ Z) C 
  --It is a extremely annoying rule to deal with. 
  --We can remove it if we generalize all other rules to allow arbitary position.
  --However, that would seemingly make all other rules equally annoying. 
  --We will stick to this commutative rule until find a better resolution.
  | wek (Δ : List PropForm) : Proof Γ A → Proof (Δ ++ Γ) A
  | contr (Δ : List PropForm) : Proof (Δ ++ Δ ++ Γ) B → Proof (Δ ++ Γ) B
  --Both weakening and contraction are structural rules because our mutliplicative cut rule.
  | rimpl : Proof (A :: Γ) B → Proof Γ (A → B)
  | limpl : Proof Γ A →  Proof (B :: Γ) C  → Proof ((A → B) :: Γ) C
  | rconj : Proof Γ A → Proof Γ B → Proof Γ (A ∧ B)
  | lconjl : Proof (A :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | lconjr : Proof (B :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | rdisjl : Proof Γ A  → Proof Γ (A ∨ B)
  | rdisjr : Proof Γ B  → Proof Γ (A ∨ B)
  | ldisj : Proof (A :: Γ) C  → Proof (B :: Γ) C → Proof ((A ∨ B) :: Γ) C 
  | cut : Proof Γ₀ A →  Proof (A :: Γ₁) B → Proof (Γ₀ ++ Γ₁) B 
  --Notice the cut rule is multiplicative while other logic rules are additive.

inductive Proof_CF : List PropForm → PropForm → Type where
  | id : Proof_CF [A] A
  | exfal : Proof_CF [⊥] A
  | com (Γ Δ : List PropForm) : Proof_CF (X ++ Γ ++ Y ++ Δ ++ Z) C → Proof_CF (X ++ Δ ++ Y ++ Γ ++ Z) C 
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