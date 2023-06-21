import Mathlib.Data.Real.Basic

--secret message hehehe

namespace sequent_calculus

--Redefine the type of propositons since Prop is not inductively defined.

inductive PropForm : Type where
  | var : ℕ → PropForm 
--| var : String → PropForm
  | neg : PropForm → PropForm
  | conj : PropForm → PropForm → PropForm
  | disj : PropForm → PropForm → PropForm

open PropForm

--Define complexity inductively for propositons.

def Complexity : PropForm → ℕ 
  | var _ => 0
  | neg P => (Complexity P) + 1
  | conj P Q =>  (Complexity P) + (Complexity Q) + 1
  | disj P Q =>  (Complexity P) + (Complexity Q) + 1

--In particular, atomic propositions are those of complexity 0.

def Atomic (P : PropForm) : Prop := Complexity P = 0 

--Create local notations for logic symbols.

prefix: 90 " & " => var 

notation : 90 " ⊥ " => conj (&0 neg (&0))

prefix: 80 " ¬ " => neg

infixl: 51 " →  " => fun (A B : PropForm) => disj (neg A) B

infixl: 53 " ∧ " => conj

infixl: 52 " ∨ " => disj

infixl: 51 " ↔ " => fun (A B : PropForm) => conj ((neg A) B) ((neg B) A)


-- infixl: 50 " ↔ " => fun (A B : PropForm) => conj (impl A B) (impl B A)

--Define proof tree of a given sequent Γ ⊢ A inductively.

inductive Proof : List PropForm → Type where
  | id : Proof [A, ¬ A]
  | com (Γ Δ : List PropForm) : Proof (X ++ Γ ++ Y ++ Δ ++ Z) → Proof (X ++ Δ ++ Y ++ Γ ++ Z)
  | wek (Δ : List PropForm) : Proof Γ → Proof (Δ ++ Γ)
  | contr (Δ : List PropForm) : Proof (Δ ++ Δ ++ Γ) → Proof (Δ ++ Γ)
  | conj : Proof ([A, B] ++ Γ)  → Proof ([conj A B] ++ Γ) 
  | disj : Proof ([A] ++ Γ) → Proof ([B] ++ Γ) → Proof ([disj A B] ++ Γ)
  | cut : Proof ([A] ++ Γ₀) →  Proof ([neg A] ++ Γ₁) → Proof (Γ₀ ++ Γ₁) 


inductive Proof_CF : List PropForm → Type where
  | id : Proof_CF [A, ¬ A]
  | com (Γ Δ : List PropForm) : Proof_CF (X ++ Γ ++ Y ++ Δ ++ Z) → Proof_CF (X ++ Δ ++ Y ++ Γ ++ Z)
  | wek (Δ : List PropForm) : Proof_CF Γ → Proof_CF (Δ ++ Γ)
  | contr (Δ : List PropForm) : Proof_CF (Δ ++ Δ ++ Γ) → Proof_CF (Δ ++ Γ)
  | conj : Proof_CF ([A, B] ++ Γ)  → Proof_CF ([conj A B] ++ Γ) 
  | disj : Proof_CF ([A] ++ Γ) → Proof_CF ([B] ++ Γ) → Proof_CF ([disj A B] ++ Γ)

--local notation for valid sequents

infixl: 40 " ⊢ " => Proof

infixl: 40 " ⊢₁ " => Proof_CF