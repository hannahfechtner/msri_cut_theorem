import Mathlib.Data.Real.Basic

--secret message hehehe

namespace LJ
open List

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
  --switch to PropForm level to significantly reduce cases  
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
  --the cut rule needs to be multiplicative to avoid conflict with wek; 

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

--several measures that help to show termination of recursions

def size {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ
  | Proof.id _ => 1
  | Proof.exfal _ => 1
  | Proof.com _ _ _ p => size p 
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

def com_size {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ 
  | Proof.id _ => 0
  | Proof.exfal _ => 0
  | Proof.com _ _ _ p => com_size p + 1
  | Proof.wek _ p => com_size p
  | Proof.contr p => com_size p
  | Proof.rimpl p => com_size p
  | Proof.limpl p q => com_size p + com_size q
  | Proof.rconj p q => com_size p + com_size q
  | Proof.lconjl _ p => com_size p
  | Proof.lconjr _ p => com_size p
  | Proof.rdisjl _ p => com_size p 
  | Proof.rdisjr _ p => com_size p
  | Proof.ldisj p q => com_size p + com_size q
  | Proof.cut p q => com_size p + com_size q

def cut_deg {Γ : List PropForm} {A : PropForm} : Proof Γ A → ℕ 
  | Proof.id _ => 0
  | Proof.exfal _ => 0
  | Proof.com _ _ _ p => cut_deg p
  | Proof.wek _ p => cut_deg p
  | Proof.contr p => cut_deg p
  | Proof.rimpl p => cut_deg p
  | Proof.limpl p q => cut_deg p + cut_deg q
  | Proof.rconj p q => cut_deg p + cut_deg q
  | Proof.lconjl _ p => cut_deg p
  | Proof.lconjr _ p => cut_deg p
  | Proof.rdisjl _ p => cut_deg p 
  | Proof.rdisjr _ p => cut_deg p
  | Proof.ldisj p q => cut_deg p + cut_deg q
  | @Proof.cut _ A _ _ p q => cut_deg p + cut_deg q + complexity A

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
  | Proof.cut p q => cut_size p + cut_size q + size p + size q

--admit strcutural com, wek, and contr for both Proof and Proof_CF

def Proof.scom (X Y Z Γ Δ : List PropForm) {A : PropForm} (p : (X ++ Γ ++ Y ++ Δ ++ Z) ⊢ A) : (X ++ Δ ++ Y ++ Γ ++ Z) ⊢ A := 
  match Γ with 
  | List.nil => match Δ with 
    | List.nil => p  
    | List.cons δ Δt => match Y with 
      | List.nil => by simpa [append_nil, nil_append] using p
      | List.cons y Yt => by
        rw [append_nil, append_cons, append_cons _ δ, append_assoc]
        apply Proof.com 
        rw [← append_assoc] 
        apply Proof.scom
        simpa using p
  | List.cons γ Γt => match Δ with
    | List.nil => match Y with
      | List.nil => by simpa [append_nil, nil_append] using p
      | List.cons y Yt => by
        rw [append_cons, append_cons _ y, append_nil, append_assoc]
        apply Proof.com 
        rw [← append_assoc] 
        apply Proof.scom
        simpa using p
    | List.cons δ Δt => by 
      rw [append_cons, append_cons _ δ, append_assoc (X ++ [δ]), append_assoc]
      apply Proof.com
      rw [← append_assoc _ Δt, append_assoc _ Y, ← append_assoc]
      apply Proof.scom
      simpa using p
termination_by Proof.scom X Y Z Γ Δ _ _ => (List.length Γ + List.length Δ + List.length Y) 

def Proof.swek {Γ : List PropForm} {A : PropForm} (Δ : List PropForm ) (p : Γ ⊢ A) : Δ ++ Γ ⊢ A :=
  match Δ with
  | List.nil => p 
  | List.cons δ Δt => Proof.wek δ (Proof.swek Δt p) 

def Proof.scontr {Γ Δ : List PropForm} {A : PropForm} (p : (Δ ++ Δ ++ Γ) ⊢ A) : Δ ++ Γ ⊢ A :=
  match Δ with
  | List.nil => p
  | List.cons δ Δt => by
    apply Proof.contr; apply Proof.scom [] [δ] Γ Δt [δ]
    rw [nil_append, append_assoc, append_assoc]
    apply Proof.scontr
    rw [← append_assoc, ← append_assoc, append_assoc Δt]
    apply Proof.scom [] (Δt ++ [δ]) Γ [δ] Δt
    simpa using p

def Proof_CF.scom (X Y Z Γ Δ : List PropForm) {A : PropForm} (p : (X ++ Γ ++ Y ++ Δ ++ Z) ⊢₁ A) : (X ++ Δ ++ Y ++ Γ ++ Z) ⊢₁ A := 
  match Γ with 
  | List.nil => match Δ with 
    | List.nil => p  
    | List.cons δ Δt => match Y with 
      | List.nil => by simpa [append_nil, nil_append] using p
      | List.cons y Yt => by
        rw [append_nil, append_cons, append_cons _ δ, append_assoc]
        apply Proof_CF.com 
        rw [← append_assoc] 
        apply Proof_CF.scom
        simpa using p
  | List.cons γ Γt => match Δ with
    | List.nil => match Y with
      | List.nil => by simpa [append_nil, nil_append] using p
      | List.cons y Yt => by
        rw [append_cons, append_cons _ y, append_nil, append_assoc]
        apply Proof_CF.com 
        rw [← append_assoc] 
        apply Proof_CF.scom
        simpa using p
    | List.cons δ Δt => by 
      rw [append_cons, append_cons _ δ, append_assoc (X ++ [δ]), append_assoc]
      apply Proof_CF.com
      rw [← append_assoc _ Δt, append_assoc _ Y, ← append_assoc]
      apply Proof_CF.scom
      simpa using p
termination_by Proof_CF.scom X Y Z Γ Δ _ _ => (List.length Γ + List.length Δ + List.length Y) 

def Proof_CF.swek {Γ : List PropForm} {A : PropForm} (Δ : List PropForm) (p : Γ ⊢₁ A) : Δ ++ Γ ⊢₁ A := 
  match Δ with
  | List.nil => p 
  | List.cons δ Δt => Proof_CF.wek δ (Proof_CF.swek Δt p) 

def Proof_CF.scontr {Γ Δ : List PropForm} {A : PropForm} (p : (Δ ++ Δ ++ Γ) ⊢₁ A) : Δ ++ Γ ⊢₁ A := 
  match Δ with
  | List.nil => p
  | List.cons δ Δt => by
    apply Proof_CF.contr; apply Proof_CF.scom [] [δ] Γ Δt [δ]
    rw [nil_append, append_assoc, append_assoc]
    apply Proof_CF.scontr
    rw [← append_assoc, ← append_assoc, append_assoc Δt]
    apply Proof_CF.scom [] (Δt ++ [δ]) Γ [δ] Δt
    simpa using p

--canonical embedding from Proof_CF to Proof

lemma CF_C {Γ : List PropForm} {A : PropForm} : (Γ ⊢₁ A) → (Γ ⊢ A)
  | Proof_CF.id _ => Proof.id _
  | Proof_CF.exfal _ => Proof.exfal _
  | Proof_CF.com _ _ _ p => Proof.com _ _ _ (CF_C p)
  | Proof_CF.wek _ p => Proof.wek _ (CF_C p)
  | Proof_CF.contr p => Proof.contr (CF_C p)
  | Proof_CF.rimpl p => Proof.rimpl (CF_C p)
  | Proof_CF.limpl p q => Proof.limpl (CF_C p) (CF_C q)
  | Proof_CF.rconj p q => Proof.rconj (CF_C p) (CF_C q)
  | Proof_CF.lconjr _ p => Proof.lconjr _ (CF_C p)
  | Proof_CF.lconjl _ p => Proof.lconjl _ (CF_C p)
  | Proof_CF.rdisjr _ p => Proof.rdisjr _ (CF_C p) 
  | Proof_CF.rdisjl _ p => Proof.rdisjl _ (CF_C p)
  | Proof_CF.ldisj p q => Proof.ldisj (CF_C p) (CF_C q)

--various inversion lemmas 

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
    apply Proof.scom [] [] Y X [A]
    simpa using (Proof.cut p (Proof.com [] [] Y (rimpl_inv q)))

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
  intro h; generalize g : (A ∧ B) :: Γ = Δ; rw [g] at h; cases h
  . injection g with gh gt
    rw [gt, ← gh]  
    exact Proof.rconj (Proof.com [] [] [] (Proof.wek B (Proof.id A))) (Proof.wek A (Proof.id B))
  . injection g; contradiction
  . sorry
  . rename_i X P p
    injection g with _ gt
    rw [gt]
    exact Proof.wek A (Proof.wek B p) 
  . sorry
  . sorry
  . injection g; contradiction
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry 
  . injection g; contradiction
  . sorry

lemma ldisj_inv {Γ : List PropForm} {A B C: PropForm} : ((A ∨ B) :: Γ ⊢ C) → A :: Γ ⊢ C × B :: Γ ⊢ C := by  
  intro h; generalize g : (A ∨ B) :: Γ = Δ; rw [g] at h; cases h
  . injection g with gh gt
    rw [gt, ← gh]  
    sorry
  . injection g; contradiction
  . sorry
  . sorry
  . sorry
  . sorry
  . injection g; contradiction
  . sorry
  . injection g; contradiction
  . injection g; contradiction
  . sorry
  . sorry 
  . sorry
  . sorry

--the main theorem 

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
      | Proof.exfal _ => by
        rw [← append_nil ([fls] ++ Γ₁), ← append_nil ([fls] ++ Γ₁), ← nil_append [fls]]
        apply Proof_CF.scom [] Γ₁ []
        simpa using (Proof_CF.swek Γ₁ (Proof_CF.exfal A))
      | Proof.com _ _ _ r => by 
        rw [append_assoc]
        apply Proof_CF.com 
        rw [← append_assoc]
        exact hauptsatz (Proof.cut r q)
      | Proof.wek _ r => Proof_CF.wek _ (hauptsatz (Proof.cut r q))
      | Proof.contr r => Proof_CF.contr (hauptsatz (Proof.cut r q))
      | Proof.limpl r s => by sorry
      | Proof.lconjr _ r => Proof_CF.lconjr _ (hauptsatz (Proof.cut r q))
      | Proof.lconjl _ r => Proof_CF.lconjl _ (hauptsatz (Proof.cut r q))
      | Proof.ldisj r s => Proof_CF.ldisj (hauptsatz (Proof.cut r q)) (hauptsatz (Proof.cut s q))
      | Proof.cut _ _ => by sorry
    | fls => match p with 
      | Proof.id _ => hauptsatz q
      | Proof.exfal _ => by
        rw [← append_nil ([fls] ++ Γ₁), ← append_nil ([fls] ++ Γ₁), ← nil_append [fls]]
        apply Proof_CF.scom [] Γ₁ []
        simpa using (Proof_CF.swek Γ₁ (Proof_CF.exfal A))
      | Proof.com _ _ _ r => by 
        rw [append_assoc]
        apply Proof_CF.com 
        rw [← append_assoc]
        exact hauptsatz (Proof.cut r q)
      | Proof.wek _ r => Proof_CF.wek _ (hauptsatz (Proof.cut r q))
      | Proof.contr r => Proof_CF.contr (hauptsatz (Proof.cut r q))
      | Proof.limpl r s => sorry
      | Proof.lconjr _ r => Proof_CF.lconjr _ (hauptsatz (Proof.cut r q))
      | Proof.lconjl _ r => Proof_CF.lconjl _ (hauptsatz (Proof.cut r q))
      | Proof.ldisj r s => Proof_CF.ldisj (hauptsatz (Proof.cut r q)) (hauptsatz (Proof.cut s q))
      | Proof.cut _ _ => by sorry
    | impl P Q => by 
      generalize g : (P → Q) :: Γ₁ = Δ; rw [g] at q; cases q 
      . injection g with gh gt; rw [gh] at p; rw [gt, append_nil]; exact hauptsatz p
      . injection g; contradiction 
      . sorry
      . rename_i _ _ r; injection g with _ gt
        rw [gt]
        exact Proof_CF.swek Γ₀ (hauptsatz r)
      . rename_i R X r; injection g with gh gt
      --contraction on the side case causes trouble: we need to perform Proof.scom within haustsatz in order to perform two cuts
      --it significantly increases the proof size; we have to count com_size seperatively from proof_size
        rw [gt]; rw [gh] at p 
        apply Proof_CF.scontr 
        have c := Proof.cut p r 
        rw [append_cons, ← append_nil Γ₀, ← nil_append Γ₀] at c
        simpa using hauptsatz (Proof.cut p (Proof.scom [] [] X Γ₀ [R] c))
      . rename_i R S r
        rw [← g] at r
        sorry
      . sorry 
      . sorry
      . injection g; contradiction 
      . injection g; contradiction 
      . sorry
      . sorry      
      . injection g; contradiction 
      . sorry
    | conj P Q => by 
      apply Proof_CF.scontr
      have c := Proof.cut ((rconj_inv p).1) (lconj_inv q)
      rw [append_cons, ← append_nil Γ₀, ← nil_append Γ₀] at c
      simpa using (hauptsatz (Proof.cut (rconj_inv p).2 ( Proof.scom [] [] Γ₁ Γ₀ [Q] c))) 
    | disj P Q => match p with 
      | Proof.id _ => hauptsatz q
      | Proof.exfal _ => by
        rw [← append_nil ([fls] ++ Γ₁), ← append_nil ([fls] ++ Γ₁), ← nil_append [fls]]
        apply Proof_CF.scom [] Γ₁ []
        simpa using (Proof_CF.swek Γ₁ (Proof_CF.exfal A))
      | Proof.com _ _ _ r => by
        rw [append_assoc]
        apply Proof_CF.com 
        rw [← append_assoc]
        exact hauptsatz (Proof.cut r q)
      | Proof.wek _ r => Proof_CF.wek _ (hauptsatz (Proof.cut r q))
      | Proof.contr r => Proof_CF.contr (hauptsatz (Proof.cut r q))
      | Proof.limpl r s => sorry
      | Proof.lconjr _ r => Proof_CF.lconjr _ (hauptsatz (Proof.cut r q))
      | Proof.lconjl _ r => Proof_CF.lconjl _ (hauptsatz (Proof.cut r q))
      | Proof.rdisjr _ _ => by sorry
      | Proof.rdisjl _ _ => by sorry
      | Proof.ldisj r s => Proof_CF.ldisj (hauptsatz (Proof.cut r q)) (hauptsatz (Proof.cut s q))
      | Proof.cut _ _ => by sorry
termination_by hauptsatz p => (cut_deg p, cut_size p, size p, com_size p)