import Mathlib.Data.Real.Basic
--trying changes
namespace sequent_calculus

--Redefine the type of propositons since Prop is not inductively defined.

inductive PropForm : Type where
  | var : ℕ → PropForm 
--| var : Sring → PropForm
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

example : Complexity (¬ ((&0 ∧ &1) → &0)) = 3 := by trivial      

--Define proof tree of a given sequent Γ ⊢ A inductively, using sequnent calculus.

inductive Proof : List PropForm → PropForm → Type where
  | id : Proof [A] A
  | exfal : Proof [⊥] A
  | com : Proof (Γ ++ A :: Δ ++ B :: θ) C →  Proof (Γ ++ B :: Δ ++ A :: θ) C 
  | wek : Proof Γ A → Proof (B :: Γ) A
  | contr : Proof (A :: A :: Γ) B → Proof (A :: Γ) B
  | rimpl : Proof (A :: Γ) B → Proof Γ (A → B)
  | limpl : Proof Γ A →  Proof (B :: Γ) C  → Proof ((A → B) :: Γ) C
  | rconj : Proof Γ A → Proof Γ B → Proof Γ (A ∧ B)
  | lconjl : Proof (A :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | lconjr : Proof (B :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | rdisjl : Proof Γ A  → Proof Γ (A ∨ B)
  | rdisjr : Proof Γ B  → Proof Γ (A ∨ B)
  | ldisj : Proof (A :: Γ) C  → Proof (B :: Γ) C → Proof ((A ∨ B) :: Γ) C 
  | cut : Proof Γ A →  Proof (A :: Γ) B → Proof Γ B 

--Define cut-free proof trees.

inductive Proof_CF : List PropForm → PropForm → Type where
  | id : Proof_CF [A] A
  | exfal : Proof_CF [⊥] A
  | com : Proof_CF (Γ ++ A :: Δ ++ B :: θ) C →  Proof_CF (Γ ++ B :: Δ ++ A :: θ) C 
  | wek : Proof_CF Γ A → Proof_CF (B :: Γ) A
  | contr : Proof_CF (A :: A :: Γ) B → Proof_CF (A :: Γ) B
  | rimpl : Proof_CF (A :: Γ) B → Proof_CF Γ (A → B)
  | limpl : Proof_CF Γ A →  Proof_CF (B :: Γ) C  → Proof_CF ((A → B) :: Γ) C
  | rconj : Proof_CF Γ A → Proof_CF Γ B → Proof_CF Γ (A ∧ B)
  | lconjl : Proof_CF (A :: Γ) C  → Proof_CF ((A ∧ B) :: Γ) C
  | lconjr : Proof_CF (B :: Γ) C  → Proof_CF ((A ∧ B) :: Γ) C
  | rdisjl : Proof_CF Γ A  → Proof_CF Γ (A ∨ B)
  | rdisjr : Proof_CF Γ B  → Proof_CF Γ (A ∨ B)
  | ldisj : Proof_CF (A :: Γ) C  → Proof_CF (B :: Γ) C → Proof_CF ((A ∨ B) :: Γ) C 

--Define size of a given proof tree, i.e., the number of inference rules used.

def Size {Γ : List PropForm} {A : PropForm} : Proof Γ A →  ℕ
  | Proof.id => 0 
  | Proof.exfal => 0
  | Proof.com H => Size H + 1
  | Proof.wek H => Size H + 1 
  | Proof.contr H => Size H + 1
  | Proof.rimpl H => Size H + 1
  | Proof.limpl H E => Size H + Size E + 1
  | Proof.rconj H E => Size H + Size E + 1
  | Proof.lconjl H => Size H +1 
  | Proof.lconjr H => Size H +1 
  | Proof.rdisjl H => Size H +1 
  | Proof.rdisjr H => Size H +1 
  | Proof.ldisj H E => Size H + Size E + 1  
  | Proof.cut H E => Size H + Size E + 1

--local notation for valid sequents

infixl: 40 
  " ⊢ " => Proof

infixl: 40 
   " ⊢₁ " => Proof_CF

--Some examples.

theorem ID : [&0] ⊢ &0 := Proof.id 

example : Size ID = 0 := by trivial

theorem modus_ponens : [&0 → &1, &0] ⊢ &1 := by 
  apply Proof.limpl
  . apply Proof.id 
  . change [] ++ &1 :: [] ++ &0 :: [] ⊢ &1
    apply Proof.com 
    apply Proof.wek
    apply Proof.id

example : Size modus_ponens = 3 := by trivial 

--More examples.

example : [&0 ∨ &1, ¬ &0] ⊢ &1 := by
  sorry

example : [&0 ∨ &1 ∧ &2] ⊢ (&0 ∨ &1) ∧ (&0 ∨ &2) := by 
  sorry 

--The main theorem.

theorem Hauptsatz (Γ : List PropForm) (A : PropForm) : (Γ ⊢ A) → (Γ ⊢₁ A) := by 
  intro h
  induction h 
  . apply Proof_CF.id 
  . apply Proof_CF.exfal
  . apply Proof_CF.com 
    rename_i last
    exact last
  . apply Proof_CF.wek
    rename_i last
    exact last
  . apply Proof_CF.contr
    rename_i last
    exact last
  . apply Proof_CF.rimpl
    rename_i last
    exact last 
  . apply Proof_CF.limpl
    rename_i second_to last
    exact second_to 
    rename_i last
    exact last
  
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  rename_i gg bju j fho hui guigu hi
  sorry