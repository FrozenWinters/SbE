{-# OPTIONS --cubical #-}

module norm where

open import lists
open import syn

data Rule : {Γ : Ctx} {A : Ty} (t s : Tm Γ A) → Type where
  β : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
    Rule (App (Lam t) s) (t [ idTms Γ ⊕ s ])
  η : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) →
    Rule t (Lam (App (t [ π ]) 𝑧))

data Occurance : (Γ : Ctx) (A : Ty) → Type where
 𝑂 : {Γ : Ctx} {A : Ty} → Occurance Γ A
 𝐿 : {Γ : Ctx} {A B : Ty} → Occurance (Γ ⊹ A) B → Occurance Γ (A ⇒ B)
 𝐴₁ : {Γ : Ctx} {A B : Ty} →
   Occurance Γ (A ⇒ B) → Tm Γ A → Occurance Γ B
 𝐴₂ : {Γ : Ctx} {A B : Ty} →
   Tm Γ (A ⇒ B) → Occurance Γ A → Occurance Γ B

O-Γ : {Γ : Ctx} {A : Ty} → Occurance Γ A → Ctx
O-Γ {Γ} 𝑂 = Γ
O-Γ (𝐿 env) = O-Γ env
O-Γ (𝐴₁ env s) = O-Γ env
O-Γ (𝐴₂ t env) = O-Γ env

O-A : {Γ : Ctx} {A : Ty} → Occurance Γ A → Ty
O-A {Γ} {A} 𝑂 = A
O-A (𝐿 env) = O-A env
O-A (𝐴₁ env s) = O-A env
O-A (𝐴₂ t env) = O-A env

O-fill : {Γ : Ctx} {A : Ty} (o : Occurance Γ A) → Tm (O-Γ o) (O-A o) → Tm Γ A
O-fill 𝑂 t = t
O-fill (𝐿 env) t = Lam (O-fill env t)
O-fill (𝐴₁ env s) t = App (O-fill env t) s 
O-fill (𝐴₂ s env) t = App s (O-fill env t)

data Step : {Γ : Ctx} {A : Ty} (t s : Tm Γ A) → Type where
  ⟨_⊚_⟩ : {Γ : Ctx} {A : Ty} (env : Occurance Γ A) {t s : Tm (O-Γ env) (O-A env)} → Rule t s →
    Step (O-fill env t) (O-fill env s)
  ⟨_⊚_⟩⁻¹ : {Γ : Ctx} {A : Ty} (env : Occurance Γ A) {t s : Tm (O-Γ env) (O-A env)} → Rule t s →
    Step (O-fill env s) (O-fill env t)
  sub⟨_⟩ : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} (a : t ≡ s) → Step t s

invertStep : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Step t s → Step s t
invertStep ⟨ env ⊚ 𝑅 ⟩ = ⟨ env ⊚ 𝑅 ⟩⁻¹
invertStep ⟨ env ⊚ 𝑅 ⟩⁻¹ = ⟨ env ⊚ 𝑅 ⟩
invertStep sub⟨ a ⟩ = sub⟨ a ⁻¹ ⟩

deepen𝐿 : {Γ : Ctx} {A B : Ty} {t s : Tm (Γ ⊹ A) B} → Step t s → Step (Lam t) (Lam s)
deepen𝐿 ⟨ env ⊚ 𝒮 ⟩ = ⟨ 𝐿 env ⊚ 𝒮 ⟩
deepen𝐿 ⟨ env ⊚ 𝒮 ⟩⁻¹ = ⟨ 𝐿 env ⊚ 𝒮 ⟩⁻¹
deepen𝐿 sub⟨ a ⟩ = sub⟨ ap Lam a ⟩

deepen𝐴₁ : {Γ : Ctx} {A B : Ty} {t s : Tm Γ (A ⇒ B)} → Step t s → (u : Tm Γ A) →
  Step (App t u) (App s u)
deepen𝐴₁ ⟨ env ⊚ 𝒮 ⟩ u = ⟨ 𝐴₁ env u ⊚ 𝒮 ⟩
deepen𝐴₁ ⟨ env ⊚ 𝒮 ⟩⁻¹ u = ⟨ 𝐴₁ env u ⊚ 𝒮 ⟩⁻¹
deepen𝐴₁ sub⟨ a ⟩ u = sub⟨ (λ i → App (a i) u) ⟩

deepen𝐴₂ : {Γ : Ctx} {A B : Ty} (u : Tm Γ (A ⇒ B)) {t s : Tm Γ A} → Step t s → 
  Step (App u t) (App u s)
deepen𝐴₂ u ⟨ env ⊚ 𝒮 ⟩ = ⟨ 𝐴₂ u env ⊚ 𝒮 ⟩
deepen𝐴₂ u ⟨ env ⊚ 𝒮 ⟩⁻¹ = ⟨ 𝐴₂ u env ⊚ 𝒮 ⟩⁻¹
deepen𝐴₂ u sub⟨ a ⟩ = sub⟨ (λ i → App u (a i)) ⟩

deepen : {Γ : Ctx} {A : Ty} (env : Occurance Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Step t s → Step (O-fill env t) (O-fill env s)
deepen env sub⟨ a ⟩ = sub⟨ ap (O-fill env) a ⟩
deepen 𝑂 ⟨ env₂ ⊚ 𝒮 ⟩ = ⟨ env₂ ⊚ 𝒮 ⟩
deepen (𝐿 env₁) ⟨ env₂ ⊚ 𝒮 ⟩ = deepen𝐿 (deepen env₁ ⟨ env₂ ⊚ 𝒮 ⟩) 
deepen (𝐴₁ env₁ u) ⟨ env₂ ⊚ 𝒮 ⟩ = deepen𝐴₁ (deepen env₁ ⟨ env₂ ⊚ 𝒮 ⟩) u
deepen (𝐴₂ u env₁) ⟨ env₂ ⊚ 𝒮 ⟩ = deepen𝐴₂ u (deepen env₁ ⟨ env₂ ⊚ 𝒮 ⟩)
deepen 𝑂 ⟨ env₂ ⊚ 𝒮 ⟩⁻¹ = ⟨ env₂ ⊚ 𝒮 ⟩⁻¹
deepen (𝐿 env₁) ⟨ env₂ ⊚ 𝒮 ⟩⁻¹ = deepen𝐿 (deepen env₁ ⟨ env₂ ⊚ 𝒮 ⟩⁻¹)
deepen (𝐴₁ env₁ u) ⟨ env₂ ⊚ 𝒮 ⟩⁻¹ = deepen𝐴₁ (deepen env₁ ⟨ env₂ ⊚ 𝒮 ⟩⁻¹) u
deepen (𝐴₂ u env₁) ⟨ env₂ ⊚ 𝒮 ⟩⁻¹ = deepen𝐴₂ u (deepen env₁ ⟨ env₂ ⊚ 𝒮 ⟩⁻¹)

infixl 20 _∷_
data Steps : {Γ : Ctx} {A : Ty} (t s : Tm Γ A) → Type where
  [] : {Γ : Ctx} {A : Ty} {t : Tm Γ A} → Steps t t
  _∷_ : {Γ : Ctx} {A : Ty} {t s r : Tm Γ A} → Steps t s → Step s r → Steps t r

deepens : {Γ : Ctx} {A : Ty} (env : Occurance Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Steps t s → Steps (O-fill env t) (O-fill env s)
deepens env [] = []
deepens env (𝒮s ∷ 𝒮) = deepens env 𝒮s ∷ deepen env 𝒮

infixl 20 _⊙_
_⊙_ : {Γ : Ctx} {A : Ty} {t s u : Tm Γ A} → Steps t s → Steps s u → Steps t u
𝒮s ⊙ [] = 𝒮s
𝒮s ⊙ (𝒯s ∷ 𝒯) = (𝒮s ⊙ 𝒯s) ∷ 𝒯

invertSteps : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Steps t s → Steps s t
invertSteps [] = []
invertSteps (𝒮s ∷ 𝒮) = [] ∷ invertStep 𝒮 ⊙ invertSteps 𝒮s

data ParallelSteps : {Γ Δ : Ctx} (σ τ : Tms Γ Δ) → Type where
  ∅𝑆 : {Γ : Ctx} → ParallelSteps (! {Γ = Γ}) !
  _⊕𝑆_ : {Γ Δ : Ctx} {A : Ty} {σ τ : Tms Γ Δ} {t s : Tm Γ A} →
    ParallelSteps σ τ → Steps t s → ParallelSteps (σ ⊕ t) (τ ⊕ s)

parallel-derive : {Γ Δ : Ctx} {A : Ty} {σ τ : Tms Γ Δ} →
  ParallelSteps σ τ → (v : Var Δ A) → Steps (derive σ v) (derive τ v)
parallel-derive (𝑆s ⊕𝑆 𝒮s) 𝑧𝑣 = 𝒮s
parallel-derive (𝑆s ⊕𝑆 𝒮s) (𝑠𝑣 v) = parallel-derive 𝑆s v

shiftRule : {Γ : Ctx} (𝑖 : CtxPos Γ) (A : Ty) {B : Ty} {t s : Tm Γ B} →
  Rule t s → Steps (shift 𝑖 {A} t) (shift 𝑖 s)
shiftRule {Γ} 𝑖 A (β t s) =
  [] ∷ ⟨ 𝑂 ⊚ β (shift (𝑆 𝑖) t) (shift 𝑖 s) ⟩
    ∷ sub⟨
      shift (𝑆 𝑖) t [ idTms (insertCtx Γ A 𝑖) ⊕ shift 𝑖 s ]
        ≡⟨ (λ i → shift (𝑆 𝑖) t [ idInsertLem Γ A 𝑖 i  ⊕ shift 𝑖 s ]) ⟩
      shift (𝑆 𝑖) t [ insertTms (𝑆 𝑖) (shiftTms 𝑖 (idTms Γ ⊕ s)) (V (varToInsertion Γ A 𝑖)) ]
        ≡⟨ shiftLem (𝑆 𝑖) t (shiftTms 𝑖 (idTms Γ ⊕ s)) (V (varToInsertion Γ A 𝑖)) ⟩
      t [ shiftTms 𝑖 (idTms Γ ⊕ s) ]
        ≡⟨ shift[] 𝑖 t (idTms Γ ⊕ s) ⁻¹ ⟩
      shift 𝑖 (t [ idTms Γ ⊕ s ])
        ∎ ⟩
shiftRule {Γ} 𝑖 A {B₁ ⇒ B₂} (η t) =
  [] ∷ ⟨ 𝑂 ⊚ η (shift 𝑖 t) ⟩
    ∷ sub⟨
      Lam (App (shift 𝑖 t [ varify (map𝑇𝑚𝑠 𝑠𝑣 (id𝑅𝑒𝑛 (insertCtx Γ A 𝑖))) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (shift 𝑖 t [ Vlem2 (id𝑅𝑒𝑛 (insertCtx Γ A 𝑖)) i ]) 𝑧)) ⟩
      Lam (App (shift 𝑖 t [ W₁Tms B₁ (idTms (insertCtx Γ A 𝑖)) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (shift 𝑖 t [ W₁Tms B₁ (idInsertLem Γ A 𝑖 i) ]) 𝑧)) ⟩
      Lam (App (shift 𝑖 t [
        W₁Tms B₁ (insertTms 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (shift 𝑖 t [
          shiftInsertLem 𝑍 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖)) i ]) 𝑧)) ⟩
      Lam (App (shift 𝑖 t [ insertTms 𝑖 (W₁Tms B₁ (shiftTms 𝑖 (idTms Γ)))
        (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (shiftLem 𝑖 t (W₁Tms B₁ (shiftTms 𝑖 (idTms Γ)))
          (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) i) 𝑧)) ⟩
      Lam (App (t [ W₁Tms B₁ (shiftTms 𝑖 (idTms Γ)) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (t [ shift²Tms (idTms Γ) 𝑍 𝑖 (~ i) ]) 𝑧)) ⟩
      Lam (App (t [ shiftTms (𝑆 𝑖) (W₁Tms B₁ (idTms Γ)) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (shift[] (𝑆 𝑖) t (Vlem2 (id𝑅𝑒𝑛 Γ) (~ i)) (~ i)) 𝑧)) ⟩
      Lam (App (shift (𝑆 𝑖) (t [ π ])) (V 𝑧𝑣))
        ∎ ⟩
        
{-# TERMINATING #-}
shiftStep : {Γ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} {t s : Tm Γ B} →
  Step t s → Steps (shift 𝑖 {A} t) (shift 𝑖 s)
shiftStep 𝑖 {A} ⟨ 𝑂 ⊚ 𝑅 ⟩ = shiftRule 𝑖 A 𝑅
shiftStep 𝑖 ⟨ 𝐿 env ⊚ 𝑅 ⟩ = deepens (𝐿 𝑂) (shiftStep (𝑆 𝑖) ⟨ env ⊚ 𝑅 ⟩)
shiftStep 𝑖 {A} ⟨ 𝐴₁ env s ⊚ 𝑅 ⟩ = deepens (𝐴₁ 𝑂 (shift 𝑖 s)) (shiftStep 𝑖 ⟨ env ⊚ 𝑅 ⟩)
shiftStep 𝑖 ⟨ 𝐴₂ t env ⊚ 𝑅 ⟩ = deepens (𝐴₂ (shift 𝑖 t) 𝑂) (shiftStep 𝑖 ⟨ env ⊚ 𝑅 ⟩)
shiftStep 𝑖 {A} ⟨ 𝑂 ⊚ 𝑅 ⟩⁻¹ = invertSteps (shiftRule 𝑖 A 𝑅)
shiftStep 𝑖 ⟨ 𝐿 env ⊚ 𝑅 ⟩⁻¹ = deepens (𝐿 𝑂) (shiftStep (𝑆 𝑖) ⟨ env ⊚ 𝑅 ⟩⁻¹)
shiftStep 𝑖 ⟨ 𝐴₁ env s ⊚ 𝑅 ⟩⁻¹ = deepens (𝐴₁ 𝑂 (shift 𝑖 s)) (shiftStep 𝑖 ⟨ env ⊚ 𝑅 ⟩⁻¹)
shiftStep 𝑖 ⟨ 𝐴₂ t env ⊚ 𝑅 ⟩⁻¹ = deepens (𝐴₂ (shift 𝑖 t) 𝑂) (shiftStep 𝑖 ⟨ env ⊚ 𝑅 ⟩⁻¹)
shiftStep 𝑖 sub⟨ a ⟩ = [] ∷ sub⟨ ap (shift 𝑖) a ⟩

shiftSteps : {Γ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} {t s : Tm Γ B} →
  Steps t s → Steps (shift 𝑖 {A} t) (shift 𝑖 s)
shiftSteps 𝑖 [] = []
shiftSteps 𝑖 (𝒮s ∷ 𝒮) = shiftSteps 𝑖 𝒮s ⊙ shiftStep 𝑖 𝒮

shiftParallel : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A : Ty} {σ τ : Tms Γ Δ} →
  ParallelSteps σ τ → ParallelSteps (shiftTms 𝑖 {A} σ) (shiftTms 𝑖 τ)
shiftParallel 𝑖 ∅𝑆 = ∅𝑆
shiftParallel 𝑖 (𝑆s ⊕𝑆 𝒮) = shiftParallel 𝑖 𝑆s ⊕𝑆 shiftSteps 𝑖 𝒮

_[_]𝑆 : {Γ Δ : Ctx} {A : Ty} {σ τ : Tms Γ Δ}
  (t : Tm Δ A) → ParallelSteps σ τ → Steps (t [ σ ]) (t [ τ ])
V v [ 𝑆s ]𝑆 = parallel-derive 𝑆s v
Lam t [ 𝑆s ]𝑆 = deepens (𝐿 𝑂) (t [ shiftParallel 𝑍 𝑆s ⊕𝑆 [] ]𝑆)
App t s [ 𝑆s ]𝑆 = deepens (𝐴₁ 𝑂 (s [ _ ])) (t [ 𝑆s ]𝑆) ⊙ deepens (𝐴₂ (t [ _ ]) 𝑂) (s [ 𝑆s ]𝑆)

data Nf : (Γ : Ctx) (A : Ty) → Type

data Ne : (Γ : Ctx) (A : Ty) → Type where
  VN : {Γ : Ctx} {A : Ty} → Var Γ A → Ne Γ A
  APP : {Γ : Ctx} {A B : Ty} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

data Nf where
  NEU : {Γ : Ctx} {c : Char} → Ne Γ (Base c) → Nf Γ (Base c)
  LAM : {Γ : Ctx} {A B : Ty} → Nf (Γ ⊹ A) B → Nf Γ (A ⇒ B)

Nes = 𝑇𝑚𝑠 Ne
Nfs = 𝑇𝑚𝑠 Nf

infix 30 _[_]NE _[_]NF
_[_]NE : {Γ Δ : Ctx} {A : Ty} → Ne Δ A → Ren Γ Δ → Ne Γ A
_[_]NF : {Γ Δ : Ctx} {A : Ty} → Nf Δ A → Ren Γ Δ → Nf Γ A

APP M N [ σ ]NE = APP (M [ σ ]NE) (N [ σ ]NF)
VN v [ σ ]NE = VN (v [ σ ]𝑅)

NEU M [ σ ]NF = NEU (M [ σ ]NE)
LAM {A = A} N [ σ ]NF = LAM (N [ W₂𝑅𝑒𝑛 A σ ]NF)

_[_]NES : {Γ Δ Σ : Ctx} → Nes Δ Σ → Ren Γ Δ → Nes Γ Σ
MS [ σ ]NES = map𝑇𝑚𝑠 _[ σ ]NE MS

_[_]NFS : {Γ Δ Σ : Ctx} → Nfs Δ Σ → Ren Γ Δ → Nfs Γ Σ
NS [ σ ]NFS = map𝑇𝑚𝑠 _[ σ ]NF NS

ιNe : {Γ : Ctx} {A : Ty} → Ne Γ A → Tm Γ A
ιNf : {Γ : Ctx} {A : Ty} → Nf Γ A → Tm Γ A

ιNe (VN v) = V v
ιNe (APP M N) = App (ιNe M) (ιNf N)

ιNf (NEU M) = ιNe M
ιNf (LAM N) = Lam (ιNf N)

ιNes : {Γ Δ : Ctx} → Nes Γ Δ → Tms Γ Δ
ιNes = map𝑇𝑚𝑠 ιNe

ιNfs : {Γ Δ : Ctx} → Nfs Γ Δ → Tms Γ Δ
ιNfs = map𝑇𝑚𝑠 ιNf

ιNeLem : {Γ Δ : Ctx} {A : Ty} (M : Ne Δ A) (σ : Ren Γ Δ) →
  ιNe (M [ σ ]NE) ≡ ιNe M [ varify σ ]
ιNfLem : {Γ Δ : Ctx} {A : Ty} (N : Nf Δ A) (σ : Ren Γ Δ) →
  ιNf (N [ σ ]NF) ≡ ιNf N [ varify σ ]

ιNeLem (VN v) σ = Vlem0 v σ
ιNeLem (APP M N) σ i = App (ιNeLem M σ i) (ιNfLem N σ i)

ιNfLem (NEU M) σ = ιNeLem M σ
ιNfLem (LAM {Γ} {A} N) σ =
  Lam (ιNf (N [ W₂𝑅𝑒𝑛 A σ ]NF))
    ≡⟨ ap Lam (ιNfLem N (W₂𝑅𝑒𝑛 A σ)) ⟩
  Lam (ιNf N [ varify (W₂𝑅𝑒𝑛 A σ) ])
    ≡⟨ (λ i → Lam (ιNf N [ Vlem2 σ i ⊕ V 𝑧𝑣 ])) ⟩
  Lam (ιNf N [ W₂Tms A (varify σ) ])
    ∎

-- ob sets of semantic presheaf
Element : Ctx → Ty → Set
Element Γ (Base X) = Nf Γ (Base X)
Element Γ (A ⇒ B) = {Δ : Ctx} → Ren Δ Γ → Element Δ A → Element Δ B

_[_]𝐸𝑙 : {Γ Δ : Ctx} {A : Ty} → Element Δ A → Ren Γ Δ → Element Γ A
_[_]𝐸𝑙 {A = Base x} 𝓈 σ = 𝓈 [ σ ]NF
_[_]𝐸𝑙 {A = A ⇒ B} 𝒻 σ τ 𝓉 = 𝒻 (σ ∘𝑅𝑒𝑛 τ) 𝓉

q : {Γ : Ctx} {A : Ty} → Element Γ A → Nf Γ A
u : {Γ : Ctx} {A : Ty} → Ne Γ A → Element Γ A

q {A = Base X} 𝓈 = 𝓈
q {Γ} {A ⇒ B} 𝒻 = LAM (q (𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))

u {A = Base X} M = NEU M
u {A = A ⇒ B} M σ 𝓈 = u (APP (M [ σ ]NE) (q 𝓈))

cmp : {Γ : Ctx} {A : Ty} (N : Ne Γ A) → Steps (ιNf (q (u N))) (ιNe N)
cmp {A = Base s} N = []
cmp {Γ} {A ⇒ B} N =
  deepens (𝐿 𝑂) (cmp (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
    ⊙ deepens (𝐿 (𝐴₂ (ιNe (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE)) 𝑂)) (cmp (VN 𝑧𝑣))
    ∷ sub⟨ (λ i → Lam (App (ιNeLem N (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) i) (V 𝑧𝑣))) ⟩
    ∷ ⟨ 𝑂 ⊚ η (ιNe N) ⟩⁻¹

Elements = 𝑇𝑚𝑠 Element

qs : {Γ Δ : Ctx} → Elements Γ Δ → Nfs Γ Δ
qs = map𝑇𝑚𝑠 q

us : {Γ Δ : Ctx} → Nes Γ Δ → Elements Γ Δ
us = map𝑇𝑚𝑠 u

cmps : {Γ Δ : Ctx} (NS : Nes Γ Δ) →
  ParallelSteps (ιNfs (qs (us NS))) (ιNes NS)
cmps ! = ∅𝑆
cmps (NS ⊕ N) = cmps NS ⊕𝑆 cmp N

_[_]𝐸𝑙𝑠 : {Γ Δ Σ : Ctx} → Elements Δ Σ → Ren Γ Δ → Elements Γ Σ
𝓈s [ σ ]𝐸𝑙𝑠 = map𝑇𝑚𝑠 _[ σ ]𝐸𝑙 𝓈s

eval-⦇α⦈ : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Elements Γ Δ → Element Γ A
eval-⦇α⦈ (V v) 𝓈s = derive 𝓈s v
eval-⦇α⦈ (Lam t) 𝓈s σ 𝓉 = eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠 ⊕ 𝓉)
eval-⦇α⦈ {Γ} (App t s) 𝓈s = eval-⦇α⦈ t 𝓈s (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s 𝓈s)

eval-nat : {Γ : Ctx} {A : Ty} (t : Tm Γ A) {Δ : Ctx} (𝓈s : Elements Δ Γ) →
  Steps (ιNf (q (eval-⦇α⦈ t 𝓈s))) (t [ ιNfs (qs 𝓈s) ])
eval-nat (V v) 𝓈s =
  [] ∷ sub⟨ ap ιNf (deriveMap q 𝓈s v) ⁻¹ ∙ deriveMap ιNf (qs 𝓈s) v ⁻¹ ⟩
eval-nat {Γ} {A ⇒ B} (Lam t) {Δ} 𝓈s =
  {!deepens (𝐿 𝑂) (eval-nat t (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠 ⊕ u (VN 𝑧𝑣)))
     !}
eval-nat (App t s) 𝓈s =
  {!eval-nat t 𝓈s!}

idNes : (Γ : Ctx) → Nes Γ Γ
idNes Γ = map𝑇𝑚𝑠 VN (id𝑅𝑒𝑛 Γ)

norm : {Γ : Ctx} {A : Ty} → Tm Γ A → Nf Γ A
norm {Γ} t = q (eval-⦇α⦈ t (us (idNes Γ)))

correctness : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
  Steps (ιNf (norm t)) t
correctness {Γ} t =
  {!eval-nat t (us (idNes Γ)) ⊙ (t [ cmps (idNes Γ) ]𝑆)!}

{-Naturality : (Γ : Ctx) (A : Ty) →
  {Δ : Ctx} → Element-}
