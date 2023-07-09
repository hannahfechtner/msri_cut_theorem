import Mathlib.Data.Real.Basic

--secret message hehehe

namespace LJ

--define the type of propositions
--notice the choice of connectives is intuitionistic

inductive PropForm : Type where
  | var : ℕ → PropForm 
--| var : String → PropForm
  | fls
  | impl : PropForm → PropForm → PropForm
  | conj : PropForm → PropForm → PropForm
  | disj : PropForm → PropForm → PropForm

open PropForm

def PropForm.neg (A : PropForm) : PropForm := impl A fls

def PropForm.equ (A B : PropForm) : PropForm := conj (impl A B) (impl B A)

--Create local notations for logic symbols.

prefix: 90 " & " => var 

notation: 70 " ⊥ " => fls

prefix: 80 " ¬ " => neg 

infixl: 51 " →  " => impl

infixl: 53 " ∧ " => conj

infixl: 52 " ∨ " => disj

infixl: 50 " ↔ " => equ

--define complexity of propositions.

def complexity : PropForm → ℕ 
  | var _ => 0
  | fls => 0
  | impl P Q =>  (complexity P) + (complexity Q) + 1
  | conj P Q =>  (complexity P) + (complexity Q) + 1
  | disj P Q =>  (complexity P) + (complexity Q) + 1

--define sequent calculus
--explicit arugments are required only if they cannot be inferred from its branches.

inductive Proof : List PropForm → PropForm → Type where
  | id (A : PropForm) : Proof [A] A
  | exfal (A : PropForm) : Proof [⊥] A
  | com (X Y Z : List PropForm) : Proof (X ++ A :: Y ++ B :: Z) C → Proof (X ++ B :: Y ++ A :: Z) C 
  | wek (B : PropForm) : Proof Γ A → Proof (B :: Γ) A
  | contr : Proof (B :: B :: Γ) A → Proof (B :: Γ) A
  | rimpl : Proof (A :: Γ) B → Proof Γ (A → B)
  | limpl : Proof Γ A →  Proof (B :: Γ) C  → Proof ((A → B) :: Γ) C
  | rconj : Proof Γ A → Proof Γ B → Proof Γ (A ∧ B)
  | lconjr (A : PropForm) : Proof (B :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | lconjl (B : PropForm) : Proof (A :: Γ) C  → Proof ((A ∧ B) :: Γ) C
  | rdisjr (A : PropForm) : Proof Γ B  → Proof Γ (A ∨ B)
  | rdisjl (B : PropForm) : Proof Γ A  → Proof Γ (A ∨ B)
  | ldisj : Proof (A :: Γ) C  → Proof (B :: Γ) C → Proof ((A ∨ B) :: Γ) C 
  | cut : Proof Γ A →  Proof (A :: Γ) B → Proof Γ B 

inductive Proof_CF : List PropForm → PropForm → Type where
  | id (A : PropForm) : Proof_CF [A] A
  | exfal (A : PropForm) : Proof_CF [⊥] A
  | com (X Y Z : List PropForm) : Proof_CF (X ++ A :: Y ++ B :: Z) C → Proof_CF (X ++ B :: Y ++ A :: Z) C 
  | wek (B : PropForm) : Proof_CF Γ A → Proof_CF (B :: Γ) A
  | contr : Proof_CF (B :: B :: Γ) A → Proof_CF (B :: Γ) A
  | rimpl : Proof_CF (A :: Γ) B → Proof_CF Γ (A → B)
  | limpl : Proof_CF Γ A →  Proof_CF (B :: Γ) C  → Proof_CF ((A → B) :: Γ) C
  | rconj : Proof_CF Γ A → Proof_CF Γ B → Proof_CF Γ (A ∧ B)
  | lconjr (A : PropForm) : Proof_CF (B :: Γ) C  → Proof_CF ((A ∧ B) :: Γ) C
  | lconjl (B : PropForm) : Proof_CF (A :: Γ) C  → Proof_CF ((A ∧ B) :: Γ) C
  | rdisjr (A : PropForm) : Proof_CF Γ B  → Proof_CF Γ (A ∨ B)  
  | rdisjl (B : PropForm) : Proof_CF Γ A  → Proof_CF Γ (A ∨ B)
  | ldisj : Proof_CF (A :: Γ) C  → Proof_CF (B :: Γ) C → Proof_CF ((A ∨ B) :: Γ) C

--local notation for valid sequents

infixl: 40 " ⊢ " => Proof

infixl: 40 " ⊢₁ " => Proof_CF

def size {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ
  | Proof.id _ => 1
  | Proof.exfal _ => 1
  | Proof.com _ _ _ p => size p + 1
  | Proof.wek _ p => size p + 1
  | Proof.contr p => size p + 1
  | Proof.rimpl p => size p +1
  | Proof.limpl p q => (size p) + (size q) + 1
  | Proof.rconj p q => (size p) + (size q) + 1
  | Proof.lconjl _ p => size p + 1
  | Proof.lconjr _ p => size p + 1
  | Proof.rdisjl _ p => size p + 1
  | Proof.rdisjr _ p => size p + 1
  | Proof.ldisj p q => (size p) + (size q) + 1
  | Proof.cut p q => (size p) + (size q) + 1

def cut_size {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ 
  | Proof.id _ => 0
  | Proof.exfal _ => 0
  | Proof.com _ _ _ p => cut_size p
  | Proof.wek _ p => cut_size p
  | Proof.contr p => cut_size p
  | Proof.rimpl p => cut_size p
  | Proof.limpl p q => (cut_size p) + (cut_size q)
  | Proof.rconj p q => (cut_size p) + (cut_size q)
  | Proof.lconjl _ p => cut_size p
  | Proof.lconjr _ p => cut_size p
  | Proof.rdisjl _ p => cut_size p 
  | Proof.rdisjr _ p => cut_size p
  | Proof.ldisj p q => (cut_size p) + (cut_size q)
  | @Proof.cut _ A _ p q => (cut_size p) + (cut_size q) + complexity A

lemma rimpl_inv {Γ : List PropForm} {A B : PropForm} : (Γ ⊢ (A → B)) →  (A :: Γ ⊢ B)
  | Proof.id _ => Proof.com [] [] [] (Proof.limpl (Proof.id A) (Proof.com [] [] [] (Proof.wek A (Proof.id B))))
  | Proof.exfal _ => Proof.wek A (@Proof.exfal B)
  | Proof.com X Y Z p => Proof.com (A :: X) Y Z (rimpl_inv p)  
  | @Proof.wek X _ P p => Proof.com [] [] X (Proof.wek P (rimpl_inv p))
  | @Proof.contr P X _ p => Proof.com [] [] X (Proof.contr (Proof.com [] [P] X (rimpl_inv p))) 
  | Proof.rimpl p => p
  | @Proof.limpl X _ _ _ p q => Proof.com [] [] X (Proof.limpl (Proof.wek A p) (Proof.com [] [] X (rimpl_inv q)))
  | @Proof.lconjr _ X _ P p => Proof.com [] [] X (Proof.lconjr P (Proof.com [] [] X (rimpl_inv p))) 
  | @Proof.lconjl _ X _ Q p => Proof.com [] [] X (Proof.lconjl Q (Proof.com [] [] X (rimpl_inv p)))  
  | @Proof.ldisj P X _ Q p q => Proof.com [] [] X (Proof.ldisj (Proof.com [] [] X (rimpl_inv p)) (Proof.com [] [] X (rimpl_inv q)))
  | @Proof.cut X P _ p q => Proof.cut (Proof.wek A p) (Proof.com [] [] X (rimpl_inv q))
 
lemma rconj_inv {Γ : List PropForm} {A B : PropForm} : (Γ ⊢ (A ∧ B)) → (Γ ⊢ A) × (Γ ⊢ B)
  | Proof.id _ => (Proof.lconjl B (Proof.id A), Proof.lconjr A (Proof.id B))
  | Proof.exfal _ => (@Proof.exfal A, @Proof.exfal B)
  | Proof.com _ _ _ p => (Proof.com _ _ _ (rconj_inv p).1, Proof.com _ _ _ (rconj_inv p).2)
  | Proof.wek P p => (Proof.wek P (rconj_inv p).1, Proof.wek P (rconj_inv p).2)
  | Proof.contr p => (Proof.contr (rconj_inv p).1, Proof.contr (rconj_inv p).2)
  | Proof.limpl p q => (Proof.limpl p (rconj_inv q).1, (Proof.limpl p (rconj_inv q).2))
  | Proof.rconj p q=> (p, q)
  | Proof.lconjr P p => (Proof.lconjr P (rconj_inv p).1, Proof.lconjr P (rconj_inv p).2)
  | Proof.lconjl Q p => (Proof.lconjl Q (rconj_inv p).1, Proof.lconjl Q (rconj_inv p).2)
  | Proof.ldisj p q => (Proof.ldisj (rconj_inv p).1 (rconj_inv q).1, (Proof.ldisj (rconj_inv p).2 (rconj_inv q).2))
  | Proof.cut p q => (Proof.cut p (rconj_inv q).1, (Proof.cut p (rconj_inv q).2))        

lemma lconj_inv {Γ : List PropForm} {A B C : PropForm} : ((A ∧ B) :: Γ ⊢ C) → (A :: B :: Γ ⊢ C) := by 
  sorry

lemma ldisj_inv {Γ : List PropForm} {A B C: PropForm} : ((A ∨ B) :: Γ ⊢ C) → ((A :: Γ ⊢ C) × (B :: Γ ⊢ C)) := by  
  sorry

theorem hauptsatz {Γ : List PropForm} {A : PropForm} : (Γ ⊢ A) → (Γ ⊢₁ A)
  | Proof.id _ => Proof_CF.id _
  | Proof.exfal _ => Proof_CF.exfal _
  | Proof.com _ _ _ p => Proof_CF.com _ _ _ (hauptsatz p) 
  | Proof.wek B p => Proof_CF.wek B (hauptsatz p)
  | Proof.contr p => Proof_CF.contr (hauptsatz p)  
  | Proof.rimpl p => Proof_CF.rimpl (hauptsatz p) 
  | Proof.limpl p q => Proof_CF.limpl (hauptsatz p) (hauptsatz q) 
  | Proof.rconj p q => Proof_CF.rconj (hauptsatz p) (hauptsatz q)
  | Proof.lconjr A p => Proof_CF.lconjr A (hauptsatz p)  
  | Proof.lconjl B p => Proof_CF.lconjl B (hauptsatz p)
  | Proof.rdisjr A p => Proof_CF.rdisjr A (hauptsatz p)
  | Proof.rdisjl B p => Proof_CF.rdisjl B (hauptsatz p)
  | Proof.ldisj p q => Proof_CF.ldisj (hauptsatz p) (hauptsatz q)
  | @Proof.cut _ B _ p q => 
    match B with 
    | var n => by sorry
    | fls => by sorry
    | impl P Q => by sorry
    | conj P Q => hauptsatz (Proof.cut (rconj_inv p).2 (Proof.cut (Proof.wek Q (rconj_inv p).1) (lconj_inv q)))
    | disj P Q => by sorry 
termination_by hauptsatz p => (cut_size p, size p)  