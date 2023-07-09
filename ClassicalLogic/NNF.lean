import Mathlib.Data.Real.Basic

--secret message hehehe

namespace SequentCalculus_NNF

--The choice of classical connectives is ¬, ∧, ∨.

inductive Lit
  | pos : ℕ → Lit
  | neg : ℕ → Lit

inductive NNForm :=
  | lit  (l : Lit)       : NNForm
  | conj (p q : NNForm) : NNForm
  | disj (p q : NNForm) : NNForm

open NNForm

def Lit.negate : Lit → Lit
  | pos n => neg n
  | neg n => pos n

def NNForm.neg : NNForm → NNForm
  | lit l    => lit l.negate
  | conj p q => disj (neg p) (neg q)
  | disj p q => conj (neg p) (neg q)

--Create local notations for logic symbols.

infixl: 53 " ∧ " => conj

infixl: 52 " ∨ " => disj

prefix: 80 " ¬ " => neg

--We recover other logical connectives using classical equivalence. Their intended logical rules are admissible. 

notation " ⊥ " => conj (Lit.pos 0) (Lit.neg 0) 

infixl: 51 " →  " => fun (A B : NNForm) => disj (neg A) B

infixl: 51 " ↔ " => fun (A B : NNForm) => conj ((neg A) B) ((neg B) A)

--Define proof tree of a given sequent Γ inductively. 
--We use one-sided sequent calculus: Γ ⊢ Δ is expessed as a sequent ⊢ ¬ Γ, Δ where ¬ Γ consists of negations of all formuals in Γ.  

inductive NnfProof : List NNForm → Type where
  | id : NnfProof [A, neg A]
  | com (Γ Δ : List NNForm) : NnfProof (X ++ Γ ++ Y ++ Δ ++ Z) → NnfProof (X ++ Δ ++ Y ++ Γ ++ Z)
  | wek (Δ : List NNForm) : NnfProof Γ → NnfProof (Δ ++ Γ)
  | contr (Δ : List NNForm) : NnfProof (Δ ++ Δ ++ Γ) → NnfProof (Δ ++ Γ)
  | conj : NnfProof ([A] ++ Γ) → NnfProof ([B] ++ Γ) → NnfProof ([conj A B] ++ Γ) 
  | disj : NnfProof ([A, B] ++ Γ)  → NnfProof ([disj A B] ++ Γ) 
  | cut : NnfProof ([A] ++ Γ₀) → NnfProof ([neg A] ++ Γ₁) → NnfProof (Γ₀ ++ Γ₁)

inductive NnfProof_CF : List NNForm → Type where
  | id : NnfProof_CF [A, neg A]
  | com (Γ Δ : List NNForm) : NnfProof_CF (X ++ Γ ++ Y ++ Δ ++ Z) → NnfProof_CF (X ++ Δ ++ Y ++ Γ ++ Z)
  | wek (Δ : List NNForm) : NnfProof_CF Γ → NnfProof_CF (Δ ++ Γ)
  | contr (Δ : List NNForm) : NnfProof_CF (Δ ++ Δ ++ Γ) → NnfProof_CF (Δ ++ Γ)
  | conj : NnfProof_CF ([A] ++ Γ) → NnfProof_CF ([B] ++ Γ) → NnfProof_CF ([conj A B] ++ Γ) 
  | disj : NnfProof_CF ([A, B] ++ Γ)  → NnfProof_CF ([disj A B] ++ Γ) 
 

--local notation for valid sequents

prefix: 40 " ⊢ " => NnfProof

prefix: 40 " ⊢₁ " => NnfProof_CF

theorem hauptsatz (Γ : List NNForm) : (⊢ Γ) → (⊢₁ Γ) := by
  intro h
  cases h 
  . rename_i A 
    apply NnfProof_CF.id
  . rename_i X Y Z Γ Δ p
    sorry
  . sorry 
  . sorry
  . sorry 
  . sorry
  . rename_i A Γ₀ Γ₁ p q 
    cases A 
    . rename_i L 
      sorry 
    . sorry 
    . sorry   