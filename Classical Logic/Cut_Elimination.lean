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

prefix: 80 " ¬ " => neg

-- infixl: 51 " →  " => impl

infixl: 53 " ∧ " => conj

infixl: 52 " ∨ " => disj

-- infixl: 50 " ↔ " => fun (A B : PropForm) => conj (impl A B) (impl B A)

--Define proof tree of a given sequent Γ ⊢ A inductively, using sequent calculus.

inductive Proof : List PropForm → Type where
  | id : Proof [A, ¬ A]
  | com (Γ Δ : List PropForm) : Proof (X ++ Γ ++ Y ++ Δ ++ Z) → Proof (X ++ Δ ++ Y ++ Γ ++ Z)
  | wek (Δ : List PropForm) : Proof Γ → Proof (Δ ++ Γ)
  | contr (Δ : List PropForm) : Proof (Δ ++ Δ ++ Γ) → Proof (Δ ++ Γ)
  | conj : Proof ([A] ++ Γ) → Proof ([B] ++ Γ) → Proof ([conj A B] ++ Γ)
  | ldisj : Proof ([A, B] ++ Γ)  → Proof ([disj A B] ++ Γ) 
  | cut : Proof ([A] ++ Γ₀) →  Proof ([neg A] ++ Γ₁) → Proof (Γ₀ ++ Γ₁) 


inductive Proof_Cf : List PropForm → Type where
  | id : Proof_Cf [A, ¬ A]
  | com (Γ Δ : List PropForm) : Proof_Cf (X ++ Γ ++ Y ++ Δ ++ Z) → Proof_Cf (X ++ Δ ++ Y ++ Γ ++ Z)
  | wek (Δ : List PropForm) : Proof_Cf Γ → Proof_Cf (Δ ++ Γ)
  | contr (Δ : List PropForm) : Proof_Cf (Δ ++ Δ ++ Γ) → Proof_Cf (Δ ++ Γ)
  | conj : Proof_Cf ([A] ++ Γ) → Proof_Cf ([B] ++ Γ) → Proof_Cf ([conj A B] ++ Γ)
  | ldisj : Proof_Cf ([A, B] ++ Γ) → Proof_Cf ([disj A B] ++ Γ) 

--local notation for valid sequents

infixl: 40 " ⊢ " => Proof

infixl: 40 " ⊢₁ " => Proof_CF