import Mathlib.Data.Real.Basic
--secret message
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

infixl: 50 " ↔ " => fun (A B : PropForm) => conj (impl A B) (impl B A)

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
  | Proof.com D => Size D + 1
  | Proof.wek D => Size D + 1 
  | Proof.contr D => Size D + 1
  | Proof.rimpl D => Size D + 1
  | Proof.limpl D E => Size D + Size E + 1
  | Proof.rconj D E => Size D + Size E + 1
  | Proof.lconjl D => Size D +1 
  | Proof.lconjr D => Size D +1 
  | Proof.rdisjl D => Size D +1 
  | Proof.rdisjr D => Size D +1 
  | Proof.ldisj D E => Size D + Size E + 1 
  | Proof.cut D E => Size D + Size E + 1

def Size_Cut {Γ : List PropForm} {A : PropForm} : Proof Γ A →  ℕ
  | Proof.id => 0 
  | Proof.exfal => 0
  | Proof.com D => Size D
  | Proof.wek D => Size D
  | Proof.contr D => Size D
  | Proof.rimpl D => Size D
  | Proof.limpl D E => Size D + Size E
  | Proof.rconj D E => Size D + Size E
  | Proof.lconjl D => Size D
  | Proof.lconjr D => Size D
  | Proof.rdisjl D => Size D
  | Proof.rdisjr D => Size D
  | Proof.ldisj D E => Size D + Size E
  | @Proof.cut Γ B A D E => Size D + Size E + Complexity B


def Data {Γ : List PropForm} {A : PropForm} (D : Proof Γ A) : ℕ × ℕ := ⟨Size D, Size_Cut D⟩ 

variable (x y : ℕ)
#check (1 : Fin 2)
--local notation for valid sequents

infixl: 40 
  " ⊢ " => Proof

infixl: 40 
   " ⊢₁ " => Proof_CF

--Some examples.

theorem identity : [&0] ⊢ &0 := Proof.id 

example : Size identity = 0 := by trivial

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

theorem disjunctive_syllogism : [&0 ∨ &1, ¬ &0] ⊢ &1 := by
  apply Proof.ldisj
  . change [] ++ &0 :: [] ++ (¬ &0) :: [] ⊢ &1
    apply Proof.com
    apply Proof.limpl
    . apply Proof.id
    . change [] ++ fls :: [] ++ &0 :: [] ⊢ &1
      apply Proof.com 
      apply Proof.wek
      apply Proof.exfal
  . change [] ++ &1 :: [] ++ (¬ &0) :: [] ⊢ &1
    apply Proof.com
    apply Proof.wek
    apply Proof.id

example : Size disjunctive_syllogism = 7 := by trivial

theorem distributativity: [] ⊢ &0 ∨ &1 ∧ &2 ↔ (&0 ∨ &1) ∧ (&0 ∨ &2) := by 
  apply Proof.rconj
  . apply Proof.rimpl
    sorry
  . apply Proof.rimpl
    apply Proof.contr
    apply Proof.lconjl
    change [] ++ (&0 ∨ &1) :: [] ++ ((&0 ∨ &1) ∧ (&0 ∨ &2)) :: _ ⊢ _
    apply Proof.com
    apply Proof.lconjr
    apply Proof.ldisj 
    . apply Proof.rdisjl 
      change [] ++ &0 :: [] ++ (&0 ∨ &1) :: _ ⊢ _
      apply Proof.com
      apply Proof.wek
      apply Proof.id
    . change [] ++ &2 :: [] ++ (&0 ∨ &1) :: _ ⊢ _
      apply Proof.com
      apply Proof.ldisj
      . apply Proof.rdisjl
        change [] ++ &0 :: [] ++ &2 :: _ ⊢ _
        apply Proof.com
        apply Proof.wek
        apply Proof.id
      . apply Proof.rdisjr 
        apply Proof.rconj
        . change [] ++ &1 :: [] ++ &2 :: _ ⊢ _
          apply Proof.com
          apply Proof.wek
          apply Proof.id
        . apply Proof.wek
          apply Proof.id

example : Size distributativity = 18 := by sorry     

--The main theorem.

theorem Hauptsatz (Γ : List PropForm) (A : PropForm) : (Γ ⊢ A) → (Γ ⊢₁ A) := by 
  intro h
  induction h 
  . apply Proof_CF.id 
  . apply Proof_CF.exfal
  . case com last => 
    apply Proof_CF.com 
    --rename_i last
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
  . next Γ A _ _ _ _ ih1 ih2 =>
    apply Proof_CF.limpl
    . exact ih1  
    exact ih2
  . apply Proof_CF.rconj
    . rename_i second_to last
      exact second_to
    rename_i last
    exact last
  . apply Proof_CF.lconjl
    rename_i last
    exact last
  . apply Proof_CF.lconjr
    rename_i last
    exact last
  . apply Proof_CF.rdisjl
    rename_i last
    exact last
  . apply Proof_CF.rdisjr
    rename_i last
    exact last
  . apply Proof_CF.ldisj
    . rename_i second_to last
      exact second_to
    rename_i last
    exact last
  -- here's the big one!
  rename_i Gamma A B Gamma_A AGamma_B two one
  induction A
  . sorry
    --this is Var(A) 
  . sorry
    --this is false
  . sorry
    --this is impl
  . rename_i six five four three
    cases Gamma_A 
    <;> sorry
    --this is conj
  sorry
    --this is disj