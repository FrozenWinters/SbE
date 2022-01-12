{-# OPTIONS --cubical #-}

module trace where

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

idParallel : {Γ Δ : Ctx} (σ : Tms Γ Δ) → ParallelSteps σ σ
idParallel ! = ∅𝑆
idParallel (σ ⊕ t) = idParallel σ ⊕𝑆 []

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

subRule : {Γ Δ : Ctx} {A : Ty} {t s : Tm Δ A} →
  Rule t s → (σ : Tms Γ Δ) → Steps (t [ σ ]) (s [ σ ])
subRule {Γ} (β t s) σ =
  [] ∷ ⟨ 𝑂 ⊚ β (t [ W₂Tms _ σ ]) (s [ σ ]) ⟩
    ∷ sub⟨
      t [ W₂Tms _ σ ] [ idTms Γ ⊕ s [ σ ] ]
        ≡⟨ [][] t (W₂Tms _ σ) (idTms Γ ⊕ s [ σ ]) ⟩
      t [ (W₁Tms _ σ) ∘Tms (idTms Γ ⊕ s [ σ ]) ⊕ s [ σ ] ]
        ≡⟨ (λ i → t [ Wlem1 σ (idTms Γ) (s [ σ ]) i ⊕ s [ σ ] ]) ⟩
      t [ σ ∘Tms idTms Γ ⊕ s [ σ ] ]
        ≡⟨ (λ i → t [ ∘TmsIdR σ i ⊕ s [ σ ] ]) ⟩
      t [ σ ⊕ s [ σ ] ]
        ≡⟨ (λ i → t [ ∘TmsIdL σ (~ i) ⊕ s [ σ ] ]) ⟩
      t [ (idTms _ ⊕ s) ∘Tms σ ]
        ≡⟨ [][] t (idTms _ ⊕ s) σ ⁻¹ ⟩
      t [ idTms _ ⊕ s ] [ σ ]
        ∎ ⟩
subRule (η t) σ =
  [] ∷ ⟨ 𝑂 ⊚ η (t [ σ ]) ⟩
    ∷ sub⟨
      Lam (App (t [ σ ] [ π ]) 𝑧)
        ≡⟨ (λ i → Lam (App ([][] t σ (Vlem2 (id𝑅𝑒𝑛 _) i) i) 𝑧)) ⟩
      Lam (App (t [ σ ∘Tms (W₁Tms _ (idTms _)) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (t [ Wlem2 σ (idTms _) i ]) 𝑧)) ⟩
      Lam (App (t [ W₁Tms _ (σ ∘Tms idTms _) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (t [ W₁Tms _ (∘TmsIdR σ i) ]) 𝑧)) ⟩
      Lam (App (t [ W₁Tms _ σ ]) 𝑧)
        ≡⟨ (λ i → Lam (App (t [ W₁Tms _ (∘TmsIdL σ (~ i)) ]) 𝑧)) ⟩
      Lam (App (t [ W₁Tms _ (idTms _ ∘Tms σ) ]) 𝑧)
        ≡⟨ (λ i → Lam (App (t [ Wlem3 (idTms _) σ (~ i) ]) 𝑧)) ⟩
      Lam (App (t [ W₁Tms _ (idTms _) ∘Tms W₂Tms _ σ ]) 𝑧)
        ≡⟨ (λ i → Lam (App ([][] t (Vlem2 (id𝑅𝑒𝑛 _) (~ i)) (W₂Tms _ σ) (~ i)) 𝑧)) ⟩
      Lam (App (t [ π ] [ W₂Tms _ σ ]) (V 𝑧𝑣))
        ∎ ⟩

{-# TERMINATING #-}
subStep : {Γ Δ : Ctx} {A : Ty} {t s : Tm Δ A} →
  Step t s → (σ : Tms Γ Δ) → Steps (t [ σ ]) (s [ σ ])
subStep ⟨ 𝑂 ⊚ 𝑅 ⟩ σ = subRule 𝑅 σ
subStep ⟨ 𝐿 env ⊚ 𝑅 ⟩ σ = deepens (𝐿 𝑂) (subStep ⟨ env ⊚ 𝑅 ⟩ (W₂Tms _ σ))
subStep ⟨ 𝐴₁ env s ⊚ 𝑅 ⟩ σ = deepens (𝐴₁ 𝑂 (s [ σ ])) (subStep ⟨ env ⊚ 𝑅 ⟩ σ)
subStep ⟨ 𝐴₂ t env ⊚ 𝑅 ⟩ σ = deepens (𝐴₂ (t [ σ ]) 𝑂) (subStep ⟨ env ⊚ 𝑅 ⟩ σ)
subStep ⟨ 𝑂 ⊚ 𝑅 ⟩⁻¹ σ = invertSteps (subRule 𝑅 σ)
subStep ⟨ 𝐿 env ⊚ 𝑅 ⟩⁻¹ σ = deepens (𝐿 𝑂) (subStep ⟨ env ⊚ 𝑅 ⟩⁻¹ (W₂Tms _ σ))
subStep ⟨ 𝐴₁ env s ⊚ 𝑅 ⟩⁻¹ σ = deepens (𝐴₁ 𝑂 (s [ σ ])) (subStep ⟨ env ⊚ 𝑅 ⟩⁻¹ σ)
subStep ⟨ 𝐴₂ t env ⊚ 𝑅 ⟩⁻¹ σ = deepens (𝐴₂ (t [ σ ]) 𝑂) (subStep ⟨ env ⊚ 𝑅 ⟩⁻¹ σ)
subStep sub⟨ a ⟩ σ = [] ∷ sub⟨ ap _[ σ ] a ⟩

_[_]𝑆' : {Γ Δ : Ctx} {A : Ty} {t s : Tm Δ A} →
  Steps t s → (σ : Tms Γ Δ) → Steps (t [ σ ]) (s [ σ ])
[] [ σ ]𝑆' = []
(𝒮s ∷ 𝒮) [ σ ]𝑆' = 𝒮s [ σ ]𝑆' ⊙ subStep 𝒮 σ
