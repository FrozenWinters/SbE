{-# OPTIONS --cubical #-}

module syn where

open import lists

data Ty : Type where
  Base : Char → Ty
  _⇒_ : Ty → Ty → Ty

Ctx = 𝐶𝑡𝑥 Ty
Var = 𝑉𝑎𝑟 Ty
Ren = 𝑅𝑒𝑛 Ty

data Tm : Ctx → Ty → Type
Tms = 𝑇𝑚𝑠 Tm

data Tm where
  V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
  Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

data CtxPos : Ctx → Type where
  𝑍 : {Γ : Ctx} → CtxPos Γ
  𝑆 : {Γ : Ctx} {A : Ty} → CtxPos Γ → CtxPos (Γ ⊹ A)

insertCtx : (Γ : Ctx) → Ty → CtxPos Γ → Ctx
insertCtx Γ A 𝑍 = Γ ⊹ A
insertCtx (Γ ⊹ B) A (𝑆 n) = insertCtx Γ A n ⊹ B

varToInsertion : (Γ : Ctx) (A : Ty) (𝑖 : CtxPos Γ) → Var (insertCtx Γ A 𝑖) A
varToInsertion Γ A 𝑍 = 𝑧𝑣
varToInsertion (Γ ⊹ B) A (𝑆 𝑖) = 𝑠𝑣 (varToInsertion Γ A 𝑖)

shiftVar : {Γ : Ctx} (𝑖 : CtxPos Γ) {B A : Ty} → Var Γ A → Var (insertCtx Γ B 𝑖) A
shiftVar 𝑍 v = 𝑠𝑣 v
shiftVar (𝑆 𝑖) 𝑧𝑣 = 𝑧𝑣
shiftVar (𝑆 𝑖) (𝑠𝑣 v) = 𝑠𝑣 (shiftVar 𝑖 v)

shiftRen : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A : Ty} → Ren Γ Δ → Ren (insertCtx Γ A 𝑖) Δ
shiftRen 𝑖 = map𝑇𝑚𝑠 (shiftVar 𝑖)

shift : {Γ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} → Tm Γ B → Tm (insertCtx Γ A 𝑖) B
shift 𝑖 (V v) = V (shiftVar 𝑖 v)
shift 𝑖 (Lam t) = Lam (shift (𝑆 𝑖) t)
shift 𝑖 (App t s) = App (shift 𝑖 t) (shift 𝑖 s)

shiftTms : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A : Ty} → Tms Γ Δ → Tms (insertCtx Γ A 𝑖) Δ
shiftTms 𝑖 = map𝑇𝑚𝑠 (shift 𝑖)

W₁Tm : {Γ : Ctx} (A : Ty) {B : Ty} → Tm Γ B → Tm (Γ ⊹ A) B
W₁Tm A t = shift 𝑍 t

W₁Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) Δ
W₁Tms A σ = map𝑇𝑚𝑠 (shift 𝑍) σ 

W₂Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) (Δ ⊹ A)
W₂Tms A σ = W₁Tms A σ ⊕ V 𝑧𝑣

infixl 30 _[_]
_[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
V v [ σ ] = derive σ v
Lam {A = A} t [ σ ] = Lam (t [ W₂Tms A σ ])
App t s [ σ ] = App (t [ σ ]) (s [ σ ])

infixl 20 _∘Tms_
_∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
σ ∘Tms τ = map𝑇𝑚𝑠 _[ τ ] σ

varify : {Γ Δ : Ctx} → Ren Γ Δ → Tms Γ Δ
varify σ = map𝑇𝑚𝑠 V σ

idTms : (Γ : Ctx) → Tms Γ Γ
idTms Γ = varify (id𝑅𝑒𝑛 Γ)

𝑧 : {Γ : Ctx} {A : Ty} → Tm (Γ ⊹ A) A
𝑧 {Γ} {A} = 𝑧𝑇𝑚𝑠 (idTms (Γ ⊹ A))

π : {Γ : Ctx} {A : Ty} → Tms (Γ ⊹ A) Γ
π {Γ} {A} = π𝑇𝑚𝑠 (idTms (Γ ⊹ A))

prefix : {Γ : Ctx} → CtxPos Γ → Ctx
prefix {Γ} 𝑍 = Γ
prefix (𝑆 𝑖) = prefix 𝑖

_+_ : {Γ : Ctx} (𝒾 : CtxPos Γ) → CtxPos (prefix 𝒾) → CtxPos Γ
𝑍 + 𝑗 = 𝑗
𝑆 𝑖 + 𝑗 = 𝑆 (𝑖 + 𝑗)

shiftPos : {Γ : Ctx} {A : Ty} (𝑖 𝑗 : CtxPos Γ) → CtxPos (insertCtx Γ A 𝑖)
shiftPos 𝑖 𝑍 = 𝑍
shiftPos 𝑍 (𝑆 𝑗) = 𝑆 (shiftPos 𝑍 𝑗)
shiftPos (𝑆 𝑖) (𝑆 𝑗) = 𝑆 (shiftPos 𝑖 𝑗)

incPos : {Γ : Ctx} {A : Ty} (𝑖 𝑗 : CtxPos Γ) → CtxPos (insertCtx Γ A 𝑖)
incPos 𝑍 𝑗 = 𝑆 𝑗
incPos (𝑆 𝑖) 𝑍 = 𝑆 𝑍
incPos (𝑆 𝑖) (𝑆 𝑗) = 𝑆 (incPos 𝑖 𝑗)

insertCtx² : {Γ : Ctx} {A B : Ty} (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  insertCtx (insertCtx Γ A 𝑖) B (incPos 𝑖 (𝑖 + 𝑗))
    ≡ insertCtx (insertCtx Γ B (𝑖 + 𝑗)) A (shiftPos (𝑖 + 𝑗) 𝑖)
insertCtx² 𝑍 𝑗 = refl
insertCtx² {Γ ⊹ A} {B} {C} (𝑆 𝑖) 𝑗 i = insertCtx² {Γ} {B} {C} 𝑖 𝑗 i ⊹ A

insertTms : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) → Tms Γ Δ → {A : Ty} → Tm Γ A → Tms Γ (insertCtx Δ A 𝑖)
insertTms 𝑍 σ t = σ ⊕ t
insertTms (𝑆 𝑖) (σ ⊕ s) t = insertTms 𝑖 σ t ⊕ s

{-insertTms² : {Γ Δ : Ctx} {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ A)
  (t : Tm Γ B) (𝑖 : CtxPos Δ) (𝑗 : CtxPos (prefix 𝑖)) →
  PathP (λ i → Tms Γ (insertCtx² {Δ} {A} {B} 𝑖 𝑗 i))
    (insertTms (incPos 𝑖 (𝑖 + 𝑗)) (insertTms 𝑖 σ s) t)
    (insertTms (shiftPos (𝑖 + 𝑗) 𝑖) (insertTms (𝑖 + 𝑗) σ t) s)
insertTms² σ s t 𝑍 𝑗 = refl
insertTms² (σ ⊕ u) s t (𝑆 𝑖) 𝑗 i = insertTms² σ s t 𝑖 𝑗 i ⊕ u-}

shiftVar² : {Γ : Ctx} {A B C : Ty} (v : Var Γ C) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  PathP (λ i → Var (insertCtx² {Γ} {A} {B} 𝑖 𝑗 i) C)
    (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) {B} (shiftVar 𝑖 {A} v))
    (shiftVar (shiftPos (𝑖 + 𝑗) 𝑖) (shiftVar (𝑖 + 𝑗) v))
shiftVar² v 𝑍 𝑗 = refl
shiftVar² 𝑧𝑣 (𝑆 𝑖) 𝑗 i = 𝑧𝑣
shiftVar² (𝑠𝑣 v) (𝑆 𝑖) 𝑗 i = 𝑠𝑣 (shiftVar² v 𝑖 𝑗 i)

shift² : {Γ : Ctx} {A B C : Ty} (t : Tm Γ C) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  PathP (λ i → Tm (insertCtx² {Γ} {A} {B} 𝑖 𝑗 i) C)
    (shift (incPos 𝑖 (𝑖 + 𝑗)) {B} (shift 𝑖 {A} t))
    (shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) t))
shift² (V v) 𝑖 𝑗 i = V (shiftVar² v 𝑖 𝑗 i)
shift² (Lam t) 𝑖 𝑗 i = Lam (shift² t (𝑆 𝑖) 𝑗 i)
shift² (App t s) 𝑖 𝑗 i = App (shift² t 𝑖 𝑗 i) (shift² s 𝑖 𝑗 i)

shift²Tms : {Γ Δ : Ctx} {A B : Ty} (σ : Tms Γ Δ) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  PathP (λ i → Tms (insertCtx² {Γ} {A} {B} 𝑖 𝑗 i) Δ)
    (shiftTms (incPos 𝑖 (𝑖 + 𝑗)) {B} (shiftTms 𝑖 {A} σ))
    (shiftTms (shiftPos (𝑖 + 𝑗) 𝑖) (shiftTms (𝑖 + 𝑗) σ))
shift²Tms ! 𝑖 𝑗 i = !
shift²Tms (σ ⊕ t) 𝑖 𝑗 i = shift²Tms σ 𝑖 𝑗 i ⊕ shift² t 𝑖 𝑗 i

deriveLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ A) (v : Var Δ B) →
  derive (insertTms 𝑖 σ s) (shiftVar 𝑖 v) ≡ derive σ v
deriveLem 𝑍 σ s v = refl
deriveLem (𝑆 𝑖) (σ ⊕ t) s 𝑧𝑣 = refl
deriveLem (𝑆 𝑖) (σ ⊕ t) s (𝑠𝑣 v) = deriveLem 𝑖 σ s v

deriveLem2 : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} (σ : Tms Γ Δ) (v : Var Δ B) →
  shift 𝑖 {A} (derive σ v) ≡ derive (shiftTms 𝑖 σ) v
deriveLem2 𝑖 (σ ⊕ t) 𝑧𝑣 = refl
deriveLem2 𝑖 (σ ⊕ t) (𝑠𝑣 v) = deriveLem2 𝑖 σ v

W₁InsertLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ B) →
  W₁Tms A (insertTms 𝑖 σ s) ≡ insertTms 𝑖 (W₁Tms A σ) (W₁Tm A s)
W₁InsertLem 𝑍 σ s = refl
W₁InsertLem (𝑆 𝑖) {A} (σ ⊕ t) s i = W₁InsertLem 𝑖 σ s i ⊕ W₁Tm A t

shiftInsertLem : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) (𝑗 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ B) →
  shiftTms 𝑖 {A} (insertTms 𝑗 σ s) ≡ insertTms 𝑗 (shiftTms 𝑖 σ) (shift 𝑖 s)
shiftInsertLem 𝑖 𝑍 σ s = refl
shiftInsertLem 𝑖 (𝑆 𝑗) (σ ⊕ t) s i = shiftInsertLem 𝑖 𝑗 σ s i ⊕ shift 𝑖 t

shiftLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  shift 𝑖 t [ insertTms 𝑖 σ s ] ≡ t [ σ ]
shiftLem 𝑖 (V v) σ s =
  deriveLem 𝑖 σ s v
shiftLem 𝑖 (Lam {Γ} {A} t) σ s =
  Lam (shift (𝑆 𝑖) t [ W₂Tms A (insertTms 𝑖 σ s) ])
    ≡⟨ (λ i → Lam (shift (𝑆 𝑖) t [ W₁InsertLem 𝑖 σ s i ⊕ 𝑧 ])) ⟩
  Lam (shift (𝑆 𝑖) t [ insertTms (𝑆 𝑖) (W₂Tms A σ) (W₁Tm A s) ])
    ≡⟨ ap Lam (shiftLem (𝑆 𝑖) t (W₂Tms A σ) (W₁Tm A s) ) ⟩
  Lam (t [ W₂Tms A σ ])
    ∎
shiftLem 𝑖 (App t₁ t₂) σ s i =
  App (shiftLem 𝑖 t₁ σ s i) (shiftLem 𝑖 t₂ σ s i)

shift[] : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) →
  shift 𝑖 {A} (t [ σ ]) ≡ (t [ shiftTms 𝑖 σ ])
shift[] 𝑖 (V v) σ =
  deriveLem2 𝑖 σ v
shift[] 𝑖 (Lam {Γ} {A} t) σ =
  Lam (shift (𝑆 𝑖) (t [ W₂Tms A σ ]))
    ≡⟨ ap Lam (shift[] (𝑆 𝑖) t (W₂Tms A σ)) ⟩
  Lam (t [ shiftTms (𝑆 𝑖) (shiftTms 𝑍 σ) ⊕ 𝑧 ])
    ≡⟨ (λ i → Lam (t [ map𝑇𝑚𝑠comp {tm₂ = Tm} (shift (𝑆 𝑖)) (shift 𝑍) σ i ⊕ 𝑧 ])) ⟩
  Lam (t [ map𝑇𝑚𝑠 (shift (𝑆 𝑖) ∘ shift 𝑍) σ ⊕ 𝑧 ])
    ≡⟨ (λ i → Lam (t [ map𝑇𝑚𝑠 (λ u → shift² u 𝑍 𝑖 i) σ ⊕ 𝑧 ])) ⟩
  Lam (t [ map𝑇𝑚𝑠 (λ u → shift 𝑍 (shift 𝑖 u)) σ ⊕ 𝑧 ])
    ≡⟨ (λ i → Lam (t [ map𝑇𝑚𝑠comp {tm₂ = Tm} (shift 𝑍) (shift 𝑖) σ (~ i) ⊕ 𝑧 ])) ⟩
  Lam (t [ W₂Tms A (shiftTms 𝑖 σ) ])
    ∎
shift[] 𝑖 (App t s) σ i =
  App (shift[] 𝑖 t σ i) (shift[] 𝑖 s σ i)
    
Wlem0 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  W₁Tm A t [ σ ⊕ s ] ≡ t [ σ ]
Wlem0 t σ s = shiftLem 𝑍 t σ s

Wlem1 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  W₁Tms A σ ∘Tms (τ ⊕ t) ≡ σ ∘Tms τ
Wlem1 ! τ t = refl
Wlem1 (σ ⊕ s) τ t i = Wlem1 σ τ t i ⊕ Wlem0 s τ t i

Wlem2 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  σ ∘Tms W₁Tms A τ ≡ W₁Tms A (σ ∘Tms τ)
Wlem2 ! τ = refl
Wlem2 {A = A} (σ ⊕ t) τ i = Wlem2 σ τ i ⊕ shift[] 𝑍 t τ (~ i) 

Wlem3 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  W₁Tms A σ ∘Tms W₂Tms A τ ≡ W₁Tms A (σ ∘Tms τ)
Wlem3 {A = A} σ τ =
  W₁Tms A σ ∘Tms (W₁Tms A τ ⊕ 𝑧)
    ≡⟨ Wlem1 σ (W₁Tms A τ) 𝑧 ⟩
  σ ∘Tms W₁Tms A τ
    ≡⟨ Wlem2 σ τ ⟩
  W₁Tms A (σ ∘Tms τ)
    ∎

Wlem4 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  (W₂Tms A σ ∘Tms W₂Tms A τ) ≡ W₂Tms A (σ ∘Tms τ)
Wlem4 σ τ i = Wlem3 σ τ i ⊕ 𝑧

[][]Var : {Γ Δ Σ : Ctx} {A : Ty} (v : Var Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  V v [ σ ] [ τ ] ≡ V v [ σ ∘Tms τ ]
[][]Var 𝑧𝑣 (σ ⊕ t) τ = refl
[][]Var (𝑠𝑣 v) (σ ⊕ t) τ = [][]Var v σ τ

[][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]
[][] (V v) σ τ = [][]Var v σ τ
[][] (Lam {Γ} {A} t) σ τ =
  Lam (t [ W₂Tms A σ ] [ W₂Tms A τ ])
    ≡⟨ ap Lam ([][] t (W₂Tms A σ) (W₂Tms A τ)) ⟩
  Lam (t [ W₂Tms A σ ∘Tms W₂Tms A τ ])
    ≡⟨ (λ i → Lam (t [ Wlem4 σ τ i ])) ⟩
  Lam (t [ W₂Tms A (σ ∘Tms τ) ])
    ∎
[][] (App t s) σ τ i = App ([][] t σ τ i) ([][] s σ τ i)

Vlem0 : {Γ Δ : Ctx} {A : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  V (v [ σ ]𝑅) ≡ (V v) [ varify σ ]
Vlem0 𝑧𝑣 (σ ⊕ w) = refl
Vlem0 (𝑠𝑣 v) (σ ⊕ w) = Vlem0 v σ

Vlem1 : {Γ Δ Σ : Ctx} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  varify (σ ∘𝑅𝑒𝑛 τ) ≡ varify σ ∘Tms varify τ
Vlem1 ! τ = refl
Vlem1 (σ ⊕ t) τ i = Vlem1 σ τ i ⊕ Vlem0 t τ i 

Vlem2 : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
  varify (W₁𝑅𝑒𝑛 A σ) ≡ W₁Tms A (varify σ)
Vlem2 ! = refl
Vlem2 (σ ⊕ v) i = Vlem2 σ i ⊕ V (𝑠𝑣 v)

Vlem2' : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A : Ty} (σ : Ren Γ Δ) →
  varify (shiftRen 𝑖 {A} σ) ≡ shiftTms 𝑖 (varify σ)
Vlem2' 𝑖 ! = refl
Vlem2' 𝑖 (σ ⊕ v) i = Vlem2' 𝑖 σ i ⊕ V (shiftVar 𝑖 v)

Vlem3 : {Γ : Ctx} {A : Ty} → W₂Tms A (idTms Γ) ≡ idTms (Γ ⊹ A)
Vlem3 {Γ} i = Vlem2 (id𝑅𝑒𝑛 Γ) (~ i) ⊕ V 𝑧𝑣

deriveW₁Ren : {Γ Δ : Ctx} {A B : Ty} (σ : Ren Γ Δ) (v : Var Δ B) →
  derive (varify (W₁𝑅𝑒𝑛 A σ)) v ≡ W₁Tm A (derive (varify σ) v)
deriveW₁Ren (σ ⊕ w) 𝑧𝑣 = refl
deriveW₁Ren (σ ⊕ w) (𝑠𝑣 v) = deriveW₁Ren σ v

deriveId : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
  derive (idTms Γ) v ≡ V v
deriveId {Γ ⊹ B} 𝑧𝑣 = refl
deriveId {Γ ⊹ B} (𝑠𝑣 v) =
  derive (varify (W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Γ))) v
    ≡⟨ deriveW₁Ren (id𝑅𝑒𝑛 Γ) v ⟩
  W₁Tm B (derive (varify (id𝑅𝑒𝑛 Γ)) v)
    ≡⟨ ap (W₁Tm B) (deriveId v) ⟩
  V (𝑠𝑣 v)
    ∎

[id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms Γ ] ≡ t

∘TmsIdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) → σ ∘Tms (idTms Γ) ≡ σ
∘TmsIdR ! = refl
∘TmsIdR (σ ⊕ t) i = ∘TmsIdR σ i ⊕ [id] t i

[id] (V v) = deriveId v
[id] (Lam {Γ} {A} t) =
  Lam (t [ W₂Tms A (idTms Γ) ])
    ≡⟨ (λ i → Lam (t [ Vlem3 i ])) ⟩
  Lam (t [ idTms (Γ ⊹ A) ])
    ≡⟨ ap Lam ([id] t) ⟩
  Lam t
    ∎
[id] (App t s) i =
  App ([id] t i) ([id] s i)

Wlem1Varify : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  varify (W₁𝑅𝑒𝑛 A σ) ∘Tms (τ ⊕ t) ≡ (varify σ) ∘Tms τ
Wlem1Varify ! τ t = refl
Wlem1Varify {A = A} (σ ⊕ v) τ t i = Wlem1Varify σ τ t i ⊕ V v [ τ ]

∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms Δ ∘Tms σ ≡ σ
∘TmsIdL ! = refl
∘TmsIdL {Γ} {Δ ⊹ B} (σ ⊕ t) =
  varify (W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Δ)) ∘Tms (σ ⊕ t) ⊕ t
    ≡⟨ (λ i → Wlem1Varify (id𝑅𝑒𝑛 Δ) σ t i ⊕ t) ⟩
  varify (id𝑅𝑒𝑛 Δ) ∘Tms σ ⊕ t
    ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
  σ ⊕ t
    ∎

idInsertLem : (Γ : Ctx) (A : Ty) (𝑖 : CtxPos Γ) →
  idTms (insertCtx Γ A 𝑖) ≡ insertTms 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))
idInsertLem Γ A 𝑍 i = Vlem2 (id𝑅𝑒𝑛 Γ) i ⊕ V 𝑧𝑣
idInsertLem (Γ ⊹ B) A (𝑆 𝑖) =
  idTms (insertCtx Γ A 𝑖 ⊹ B)
    ≡⟨ (λ i → Vlem2 (id𝑅𝑒𝑛 (insertCtx Γ A 𝑖)) i ⊕ V 𝑧𝑣) ⟩
  W₁Tms B (idTms (insertCtx Γ A 𝑖)) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → W₁Tms B (idInsertLem Γ A 𝑖 i) ⊕ V 𝑧𝑣) ⟩
  W₁Tms B (insertTms 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → W₁InsertLem 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖)) i ⊕ V 𝑧𝑣) ⟩
  insertTms 𝑖 (W₁Tms B (shiftTms 𝑖 (idTms Γ))) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → insertTms 𝑖 (shift²Tms (idTms Γ) 𝑍 𝑖 (~ i)) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣) ⟩
  insertTms 𝑖 (shiftTms (𝑆 𝑖) (W₁Tms B (idTms Γ))) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → insertTms 𝑖 (shiftTms (𝑆 𝑖) (Vlem2 (id𝑅𝑒𝑛 Γ) (~ i)))
      (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣) ⟩
  insertTms (𝑆 𝑖) (shiftTms (𝑆 𝑖) (idTms (Γ ⊹ B))) (V (varToInsertion (Γ ⊹ B) A (𝑆 𝑖)))
    ∎

{-π[] : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) (t : Tm Γ A) →
  π ∘Tms (σ ⊕ t) ≡ σ
π[] {Γ} {Δ} σ t =
  π ∘Tms (σ ⊕ t)
    ≡⟨ Wlem1Varify (id𝑅𝑒𝑛 Δ) σ t ⟩
  idTms Δ ∘Tms σ
    ≡⟨ ∘TmsIdL σ ⟩
  σ
    ∎

[]lem : {Γ : Ctx} {A B C : Ty} (t : Tm (Γ ⊹ B) C) (s : Tm (Γ ⊹ A) B) (u : Tm Γ A) →
  t [ π ⊕ s ] [ idTms Γ ⊕ u ] ≡ t [ idTms Γ ⊕ s [ idTms Γ ⊕ u ] ]
[]lem {Γ} t s u =
  t [ π ⊕ s ] [ idTms Γ ⊕ u ]
    ≡⟨ [][] t (π ⊕ s) (idTms Γ ⊕ u) ⟩
  t [ π ∘Tms (idTms Γ ⊕ u) ⊕ s [ idTms Γ ⊕ u ] ]
    ≡⟨ (λ i → t [ π[] (idTms Γ) u i  ⊕ s [ idTms Γ ⊕ u ] ]) ⟩
  t [ idTms Γ ⊕ s [ idTms Γ ⊕ u ] ]
    ∎-}
