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
  | fls => 0
  | impl P Q =>  complexity P + complexity Q + 1
  | conj P Q =>  complexity P + complexity Q + 1
  | disj P Q =>  complexity P + complexity Q + 1

--define sequent calculus
--explicit arugments are required only if they cannot be inferred from its branches.

inductive Proof : List PropForm → PropForm → Type where
  | id (A : PropForm) : Proof [A] A
  | exfal (A : PropForm) : Proof [⊥] A
  | com (X Y Z : List PropForm) : Proof (X ++ [A] ++ Y ++ [B] ++ Z) C → Proof (X ++ [B] ++ Y ++ [A] ++ Z) C 
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
  | cut : Proof Γ₀ A →  Proof (A :: Γ₁) B → Proof (Γ₀ ++ Γ₁) B 

inductive Proof_CF : List PropForm → PropForm → Type where
  | id (A : PropForm) : Proof_CF [A] A
  | exfal (A : PropForm) : Proof_CF [⊥] A
  | com (X Y Z : List PropForm) : Proof_CF (X ++ [A] ++ Y ++ [B] ++ Z) C → Proof_CF (X ++ [B] ++ Y ++ [A] ++ Z) C 
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
  | Proof.limpl p q => size p + size q + 1
  | Proof.rconj p q => size p + size q + 1
  | Proof.lconjl _ p => size p + 1
  | Proof.lconjr _ p => size p + 1
  | Proof.rdisjl _ p => size p + 1
  | Proof.rdisjr _ p => size p + 1
  | Proof.ldisj p q => size p + size q + 1
  | Proof.cut p q => size p + size q + 1

def cut_size {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ 
  | Proof.id _ => 0
  | Proof.exfal _ => 0
  | Proof.com _ _ _ p => cut_size p
  | Proof.wek _ p => cut_size p
  | Proof.contr p => cut_size p
  | Proof.rimpl p => cut_size p
  | Proof.limpl p q => cut_size p + cut_size q
  | Proof.rconj p q => cut_size p + cut_size q
  | Proof.lconjl _ p => cut_size p
  | Proof.lconjr _ p => cut_size p
  | Proof.rdisjl _ p => cut_size p 
  | Proof.rdisjr _ p => cut_size p
  | Proof.ldisj p q => cut_size p + cut_size q
  | @Proof.cut _ A _ _ p q => cut_size p + cut_size q + complexity A

def Proof.scom (X Y Z Γ Δ : List PropForm) {A : PropForm} (p : (X ++ Γ ++ Y ++ Δ ++ Z) ⊢ A) : (X ++ Δ ++ Y ++ Γ ++ Z) ⊢ A := by
  sorry

def Proof.swek {Γ : List PropForm} {A : PropForm} (Δ : List PropForm ) (p : Γ ⊢ A) : Δ ++ Γ ⊢ A := by
  sorry

def Proof.scontr {Γ Δ : List PropForm} {A : PropForm} (p : (Δ ++ Δ ++ Γ) ⊢ A) : Δ ++ Γ ⊢ A := by
  sorry

def Proof_CF.scom (X Y Z Γ Δ : List PropForm) {A : PropForm} (p : (X ++ Γ ++ Y ++ Δ ++ Z) ⊢₁ A) : (X ++ Δ ++ Y ++ Γ ++ Z) ⊢₁ A := by
  sorry
--   cases Γ
--   . cases Δ 
--     . assumption 
--     . rename_i P Δ 
--       cases Y
--       . simpa [List.append_nil, List.nil_append] using p
--       . rename_i Q Y 
--         change X ++ ([P] ++ Δ) ++ ([Q] ++ Y) ++ [] ++ Z ⊢₁ A
--         rw [List.append_nil, ← List.append_assoc X, ← List.append_assoc, List.append_assoc]
--         apply Proof_CF.com 
--         rw [← List.append_assoc] 
--         apply struct_com_CF
--         change X ++ [] ++ ([Q] ++ Y) ++ ([P] ++ Δ) ++ Z ⊢₁ A at p
--         rw [List.append_nil, ← List.append_assoc X, ← List.append_assoc _ [P]] at p
--         assumption
--   . rename_i P Γ 
--     cases Δ 
--     . cases Y 
--       . simpa [List.append_nil, List.nil_append] using p
--       . rename_i Q Y 
--         change X ++ [] ++ ([Q] ++ Y) ++ ([P] ++ Γ) ++ Z ⊢₁ A
--         rw [List.append_nil, ← List.append_assoc X, ← List.append_assoc, List.append_assoc]
--         apply Proof_CF.com 
--         rw [← List.append_assoc] 
--         apply struct_com_CF
--         change X ++ ([P] ++ Γ) ++ ([Q] ++ Y) ++ [] ++ Z ⊢₁ A at p
--         rw [List.append_nil, ← List.append_assoc X, ← List.append_assoc _ [Q]] at p
--         assumption
--     . rename_i Q Δ 
--       change X ++ ([Q] ++ Δ) ++ Y ++ ([P] ++ Γ) ++ Z ⊢₁ A 
--       rw [← List.append_assoc X, List.append_assoc _ Δ, ← List.append_assoc, List.append_assoc]
--       apply Proof_CF.com
--       rw [← List.append_assoc _ Δ, List.append_assoc _ Y, ← List.append_assoc]
--       apply struct_com_CF
--       change  X ++ ([P] ++ Γ) ++ Y ++ ([Q] ++ Δ) ++ Z ⊢₁ A at p
--       rw [← List.append_assoc X, ← List.append_assoc _ [Q], List.append_assoc _ Y] at p
--       assumption
-- termination_by struct_com_CF X Y Z Γ Δ A p => (List.length Γ + List.length Δ) 

def Proof_CF.swek {Γ : List PropForm} {A : PropForm} (Δ : List PropForm) (p : Γ ⊢₁ A) : Δ ++ Γ ⊢₁ A := by
  sorry

def Proof_CF.scontr {Γ : List PropForm} {A : PropForm} (p : (Δ ++ Δ ++ Γ) ⊢₁ A) : Δ ++ Γ ⊢₁ A := by
  sorry

lemma rimpl_inv {Γ : List PropForm} {A B : PropForm} : (Γ ⊢ A → B) →  A :: Γ ⊢ B
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
  | @Proof.cut X P Y _ p q => by 
    change [A] ++ X ++ Y ⊢ B 
    apply Proof.scom [] [] Y X [A]
    have ic := Proof.cut p (Proof.com [] [] Y (rimpl_inv q))
    simpa using ic 

lemma rconj_inv {Γ : List PropForm} {A B : PropForm} : (Γ ⊢ A ∧ B) → Γ ⊢ A × Γ ⊢ B
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

lemma lconj_inv {Γ : List PropForm} {A B C : PropForm} : ((A ∧ B) :: Γ ⊢ C) → A :: B :: Γ ⊢ C := by 
  intro h
  generalize g : (A ∧ B) :: Γ = Δ 
  rw [g] at h
  sorry

lemma ldisj_inv {Γ : List PropForm} {A B C: PropForm} : ((A ∨ B) :: Γ ⊢ C) → A :: Γ ⊢ C × B :: Γ ⊢ C := by  
  intro h
  generalize g : (A ∨ B) :: Γ = Δ 
  rw [g] at h
  sorry

theorem hauptsatz {Γ : List PropForm} {A : PropForm} : (Γ ⊢ A) → Γ ⊢₁ A
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
  | @Proof.cut Γ₀ B Γ₁ _ p q => match B with 
    | var n => match p with 
      | Proof.id _ => hauptsatz q
      | Proof.exfal _ => by sorry
        -- change [] ++ [fls] ++ [] ++ Γ₁ ⊢₁ A
        -- rw [← List.append_nil ([] ++ [fls] ++ [] ++ Γ₁)]
        -- apply Proof_CF.scom [] [] [] Γ₁ [fls]
        -- rw [List.nil_append, List.append_nil, List.append_nil]
        -- apply (Proof_CF.swek Γ₁ (Proof_CF.exfal A))
      | Proof.com _ _ _ _ => by sorry
      | Proof.wek _ _ => by sorry
      | Proof.contr _ => by sorry
      | Proof.limpl _ _ => by sorry
      | Proof.lconjr _ _ => by sorry
      | Proof.lconjl _ _ => by sorry
      | Proof.ldisj _ _ => by sorry
      | Proof.cut _ _ => by sorry
    | fls => match p with 
      | Proof.id _ => hauptsatz q
      | Proof.exfal _ => by sorry
      | Proof.com _ _ _ _ => by sorry
      | @Proof.wek X _ C r => by sorry
      | @Proof.contr C X _ r => by sorry 
      | Proof.limpl _ _ => by sorry
      | Proof.lconjr _ _ => by sorry
      | Proof.lconjl _ _ => by sorry
      | Proof.ldisj _ _ => by sorry
      | Proof.cut _ _ => by sorry
    | impl P Q => by 
      generalize g : (P → Q) :: Γ₁ = Δ 
      rw [g] at q
      cases q 
      . injection g with gh 
        rw [gh] at p 
        sorry 
      . injection g
        contradiction 
      . sorry
      . sorry 
      . sorry
      . sorry      
      . sorry 
      . sorry
      . injection g
        contradiction 
      . injection g
        contradiction 
      . sorry
      . sorry      
      . injection g
        contradiction 
      . sorry
    | conj P Q => by sorry
      --have := hauptsatz (Proof.cut (rconj_inv p).2 (Proof.cut ((rconj_inv p).1) (lconj_inv q)))
    | disj P Q => match p with 
      | Proof.id _ => hauptsatz q
      | Proof.exfal _ => by sorry 
      | Proof.com _ _ _ _ => by sorry
      | Proof.wek _ _ => by sorry
      | Proof.contr _ => by sorry
      | Proof.limpl _ _ => by sorry
      | Proof.lconjr _ _ => by sorry
      | Proof.lconjl _ _ => by sorry
      | Proof.rdisjr _ _ => by sorry
      | Proof.rdisjl _ _ => by sorry
      | Proof.ldisj _ _ => by sorry
      | Proof.cut _ _ => by sorry
termination_by hauptsatz p => (cut_size p, size p)