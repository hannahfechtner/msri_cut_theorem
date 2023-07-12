import Mathlib.Data.Real.Basic

--secret message hehehe

namespace LK

--define the type of propositions
--notice the choice of connectives is classcial

inductive PropForm : Type where
  | var : ℕ → PropForm 
--| var : String → PropForm
  | neg : PropForm → PropForm
  | conj : PropForm → PropForm → PropForm
  | disj : PropForm → PropForm → PropForm

open PropForm

def PropForm.fls : PropForm := conj (var 0) (neg (var 0))

def PropForm.impl (A B : PropForm) : PropForm := disj (neg A) B 

def PropForm.equiv (A B : PropForm) : PropForm := conj (impl A B) (impl B A)

--Create local notations for logic symbols.

prefix: 90 " & " => var 

notation: 70 " ⊥ " => fls

prefix: 80 " ¬ " => neg 

infixl: 51 " →  " => impl

infixl: 53 " ∧ " => conj

infixl: 52 " ∨ " => disj

infixl: 50 " ↔ " => equiv

--define complexity of propositions.

def complexity : PropForm → ℕ 
  | var _ => 0
  | neg P => complexity P + 1
  | conj P Q => complexity P + complexity Q + 1
  | disj P Q => complexity P + complexity Q + 1

--define sequent calculus
--explicit arugments are required only if they cannot be inferred from its branches.

inductive Proof : List PropForm → List PropForm → Type where
  | id (A : PropForm) : Proof [A] [A]
  | rcom (X Y Z : List PropForm) : Proof Γ (X ++ A :: Y ++ B :: Z) → Proof Γ (X ++ B :: Y ++ A :: Z)
  | lcom (X Y Z : List PropForm) : Proof (X ++ A :: Y ++ B :: Z) Δ → Proof (X ++ B :: Y ++ A :: Z) Δ 
  | rwek (B : PropForm) : Proof Γ Δ → Proof Γ (B :: Δ)
  | lwek (B : PropForm) : Proof Γ Δ → Proof (B :: Γ) Δ 
  | rneg : Proof (A :: Γ) Δ → Proof Γ ((¬ A) :: Δ)
  | lneg : Proof Γ (A :: Δ) → Proof ((¬ A) :: Γ) Δ
  | rcontr : Proof Γ (B :: B :: Δ) → Proof Γ (B :: Δ)
  | lcontr : Proof (B :: B :: Γ) Δ → Proof (B :: Γ) Δ
  | rconj : Proof Γ (A :: Δ) → Proof Γ (B :: Δ) → Proof Γ ((A ∧ B) :: Δ)
  | lconj : Proof (A :: B :: Γ) Δ  → Proof ((A ∧ B) :: Γ) Δ
  | rdisj : Proof Γ (A :: B :: Δ )  → Proof Γ ((A ∨ B) :: Δ) 
  | ldisj : Proof (A :: Γ) Δ  → Proof (B :: Γ) Δ → Proof ((A ∨ B) :: Γ) Δ
  | cut : Proof Γ₀ (A :: Δ₀)  →  Proof (A :: Γ₁) Δ₁  → Proof (Γ₀ ++ Γ₁) (Δ₀ ++ Δ₁)

inductive Proof_CF : List PropForm → List PropForm → Type where
  | id (A : PropForm) : Proof_CF [A] [A]
  | rcom (X Y Z : List PropForm) : Proof_CF Γ (X ++ A :: Y ++ B :: Z) → Proof_CF Γ (X ++ B :: Y ++ A :: Z)
  | lcom (X Y Z : List PropForm) : Proof_CF (X ++ A :: Y ++ B :: Z) Δ → Proof_CF (X ++ B :: Y ++ A :: Z) Δ 
  | rwek (B : PropForm) : Proof_CF Γ Δ → Proof_CF Γ (B :: Δ)
  | lwek (B : PropForm) : Proof_CF Γ Δ → Proof_CF (B :: Γ) Δ 
  | rneg : Proof_CF (A :: Γ) Δ → Proof_CF Γ ((¬ A) :: Δ)
  | lneg : Proof_CF Γ (A :: Δ) → Proof_CF ((¬ A) :: Γ) Δ  
  | rcontr : Proof_CF Γ (B :: B :: Δ) → Proof_CF Γ (B :: Δ)
  | lcontr : Proof_CF (B :: B :: Γ) Δ → Proof_CF (B :: Γ) Δ
  | rconj : Proof_CF Γ (A :: Δ) → Proof_CF Γ (B :: Δ) → Proof_CF Γ ((A ∧ B) :: Δ)
  | lconj : Proof_CF (A :: B :: Γ) Δ  → Proof_CF ((A ∧ B) :: Γ) Δ
  | rdisj : Proof_CF Γ (A :: B :: Δ )  → Proof_CF Γ ((A ∨ B) :: Δ) 
  | ldisj : Proof_CF (A :: Γ) Δ  → Proof_CF (B :: Γ) Δ → Proof_CF ((A ∨ B) :: Γ) Δ

--local notation for valid sequents

infixl: 40 " ⊢ " => Proof

infixl: 40 " ⊢₁ " => Proof_CF

def size {Γ : List PropForm} {Δ : List PropForm} : Proof Γ Δ  → ℕ
  | Proof.id _ => 1
  | Proof.rcom _ _ _ p => size p + 1
  | Proof.lcom _ _ _ p => size p + 1  
  | Proof.rwek _ p => size p + 1
  | Proof.lwek _ p => size p + 1  
  | Proof.rcontr p => size p + 1
  | Proof.lcontr p => size p + 1  
  | Proof.rneg p => size p + 1
  | Proof.lneg p => size p + 1  
  | Proof.rconj p q => size p + size q + 1
  | Proof.lconj p => size p + 1  
  | Proof.rdisj p => size p + 1
  | Proof.ldisj p q => size p + size q + 1
  | Proof.cut p q => size p + size q + 1

def cut_size {Γ : List PropForm} {Δ : List PropForm} : Proof Γ Δ  → ℕ
  | Proof.id _ => 0
  | Proof.rcom _ _ _ p => cut_size p 
  | Proof.lcom _ _ _ p => cut_size p
  | Proof.rwek _ p => cut_size p
  | Proof.lwek _ p => cut_size p
  | Proof.rcontr p => cut_size p
  | Proof.lcontr p => cut_size p
  | Proof.rneg p => size p
  | Proof.lneg p => size p   
  | Proof.rconj p q => cut_size p + cut_size q
  | Proof.lconj p => cut_size p
  | Proof.rdisj p => cut_size p
  | Proof.ldisj p q => cut_size p + cut_size q
  | @Proof.cut _ A _ _ _ p q => cut_size p + cut_size q + complexity A

lemma rneg_inv {Γ Δ : List PropForm} {A : PropForm} : (Γ ⊢ (¬ A) :: Δ) → A :: Γ ⊢ Δ := by 
  sorry 

lemma lneg_inv {Γ Δ : List PropForm} {A : PropForm} : ((¬ A) :: Γ ⊢ Δ) → Γ ⊢ A :: Δ := by 
  sorry

lemma rconj_inv {Γ Δ : List PropForm} {A B : PropForm} : (Γ ⊢ (A ∧ B) :: Δ) → Γ ⊢ A :: Δ × Γ ⊢ B :: Δ := by 
  sorry

lemma lconj_inv {Γ Δ : List PropForm} {A B : PropForm} : ((A ∧ B) :: Γ ⊢ Δ) → A :: B :: Γ ⊢ Δ := by 
  sorry

lemma rdisj_inv {Γ Δ : List PropForm} {A B : PropForm} : (Γ ⊢ (A ∨ B) :: Δ) → Γ ⊢ A :: B :: Δ := by 
  sorry  

lemma ldisj_inv {Γ Δ : List PropForm} {A B : PropForm} : ((A ∨ B) :: Γ ⊢ Δ) → A :: Γ ⊢ Δ × B :: Γ ⊢ Δ := by 
  sorry

theorem hauptsatz {Γ Δ : List PropForm} : (Γ ⊢ Δ) → Γ ⊢₁ Δ
  | Proof.id _ => Proof_CF.id _
  | Proof.rcom _ _ _ p => Proof_CF.rcom _ _ _ (hauptsatz p) 
  | Proof.lcom _ _ _ p => Proof_CF.lcom _ _ _ (hauptsatz p)   
  | Proof.rwek B p => Proof_CF.rwek B (hauptsatz p)
  | Proof.lwek B p => Proof_CF.lwek B (hauptsatz p)  
  | Proof.rcontr p => Proof_CF.rcontr (hauptsatz p)  
  | Proof.lcontr p => Proof_CF.lcontr (hauptsatz p)    
  | Proof.rneg p => Proof_CF.rneg (hauptsatz p) 
  | Proof.lneg p => Proof_CF.lneg (hauptsatz p)   
  | Proof.rconj p q => Proof_CF.rconj (hauptsatz p) (hauptsatz q)
  | Proof.lconj p => Proof_CF.lconj (hauptsatz p)  
  | Proof.rdisj p => Proof_CF.rdisj (hauptsatz p)
  | Proof.ldisj p q => Proof_CF.ldisj (hauptsatz p) (hauptsatz q)
  | @Proof.cut _ B _ _ _ p q => 
    match B with 
    | var n => by sorry
    | neg P => by sorry
    | conj P Q => by sorry
    | disj P Q => by sorry 