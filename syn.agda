module syn where

open import lists

open import Agda.Builtin.Char public

infixr 20 _⇒_
data Ty : Type lzero where
  Base : Char → Ty
  _⇒_ : Ty → Ty → Ty

Ctx = 𝐶𝑡𝑥 Ty
Var = 𝑉𝑎𝑟 Ty
Ren = 𝑅𝑒𝑛 Ty

data Tm : Ctx → Ty → Type lzero
Tms = 𝑇𝑚𝑠 Tm

data Tm where
  V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
  Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

data CtxPos : Ctx → Type lzero where
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
insertCtx² {Γ ⊹ A} {B} {C} (𝑆 𝑖) 𝑗 = ap (_⊹ A) (insertCtx² {Γ} {B} {C} 𝑖 𝑗)

insertTms : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) → Tms Γ Δ → {A : Ty} → Tm Γ A → Tms Γ (insertCtx Δ A 𝑖)
insertTms 𝑍 σ t = σ ⊕ t
insertTms (𝑆 𝑖) (σ ⊕ s) t = insertTms 𝑖 σ t ⊕ s

-- The following few lemmas are more general than they need to be

tr𝑧𝑣 : {Γ Δ : Ctx} {A : Ty} (p : Γ ≡ Δ) → tr (λ Σ → Var Σ A) (ap (_⊹ A) p) 𝑧𝑣 ≡ 𝑧𝑣
tr𝑧𝑣 refl = refl

tr𝑠𝑣 : {Γ Δ : Ctx} {A B : Ty} (p : Γ ≡ Δ) (v : Var Γ B) →
  tr (λ Σ → Var Σ B) (ap (_⊹ A) p) (𝑠𝑣 v) ≡ 𝑠𝑣 (tr (λ Σ → Var Σ B) p v)
tr𝑠𝑣 refl v = refl

shiftVar² : {Γ : Ctx} {A B C : Ty} (v : Var Γ C) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  tr (λ Σ → Var Σ C) (insertCtx² {Γ} {A} {B} 𝑖 𝑗) (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) (shiftVar 𝑖 v))
    ≡ (shiftVar (shiftPos (𝑖 + 𝑗) 𝑖) (shiftVar (𝑖 + 𝑗) v))
shiftVar² v 𝑍 𝑗 = refl
shiftVar² 𝑧𝑣 (𝑆 𝑖) 𝑗 = tr𝑧𝑣 (insertCtx² 𝑖 𝑗)
shiftVar² {Γ ⊹ A} {C = C} (𝑠𝑣 v) (𝑆 𝑖) 𝑗 =
  tr (λ Σ → Var Σ C) (ap (_⊹ A) (insertCtx² 𝑖 𝑗)) (𝑠𝑣 (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) (shiftVar 𝑖 v)))
    ≡⟨ tr𝑠𝑣 (insertCtx² 𝑖 𝑗) (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) (shiftVar 𝑖 v)) ⟩
  𝑠𝑣 (tr (λ Σ → Var Σ C) (insertCtx² 𝑖 𝑗) (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) (shiftVar 𝑖 v)))
    ≡⟨ ap 𝑠𝑣 (shiftVar² v 𝑖 𝑗) ⟩
  𝑠𝑣 (shiftVar (shiftPos (𝑖 + 𝑗) 𝑖) (shiftVar (𝑖 + 𝑗) v))
    ∎

trV : {Γ Δ : Ctx} {A : Ty} (p : Γ ≡ Δ) (v : Var Γ A) →
  tr (λ Σ → Tm Σ A) p (V v) ≡ V (tr (λ Σ → Var Σ A) p v)
trV refl v = refl

trLam : {Γ Δ : Ctx} {A B : Ty} (p : Γ ≡ Δ) (t : Tm (Γ ⊹ A) B) →
  tr (λ Σ → Tm Σ (A ⇒ B)) p (Lam t) ≡ Lam (tr (λ Σ → Tm Σ B) (ap (_⊹ A) p) t)
trLam refl t = refl

trApp : {Γ Δ : Ctx} {A B : Ty} (p : Γ ≡ Δ) (t : Tm Γ (A ⇒ B)) (s : Tm Γ A) →
  tr (λ Σ → Tm Σ B) p (App t s) ≡ App (tr (λ Σ → Tm Σ (A ⇒ B)) p t) (tr (λ Σ → Tm Σ A) p s)
trApp refl t s = refl

shift² : {Γ : Ctx} {A B C : Ty} (t : Tm Γ C) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  tr (λ Σ → Tm Σ C) (insertCtx² {Γ} {A} {B} 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t))
    ≡ (shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) t))
shift² {C = C} (V v) 𝑖 𝑗 =
  tr (λ Σ → Tm Σ C) (insertCtx² 𝑖 𝑗) (V (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) (shiftVar 𝑖 v)))
    ≡⟨ trV (insertCtx² 𝑖 𝑗) (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) (shiftVar 𝑖 v)) ⟩
  V (tr (λ Σ → Var Σ C) (insertCtx² 𝑖 𝑗) (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) (shiftVar 𝑖 v)))
    ≡⟨ ap V (shiftVar² v 𝑖 𝑗) ⟩
  V (shiftVar (shiftPos (𝑖 + 𝑗) 𝑖) (shiftVar (𝑖 + 𝑗) v))
    ∎
shift² {C = A ⇒ B} (Lam t) 𝑖 𝑗 =
  tr (λ Σ → Tm Σ (A ⇒ B)) (insertCtx² 𝑖 𝑗) (Lam (shift (𝑆 (incPos 𝑖 (𝑖 + 𝑗))) (shift (𝑆 𝑖) t)))
    ≡⟨ trLam (insertCtx² 𝑖 𝑗) (shift (𝑆 (incPos 𝑖 (𝑖 + 𝑗))) (shift (𝑆 𝑖) t)) ⟩
  Lam (tr (λ Σ → Tm Σ B) (ap (_⊹ A) (insertCtx² 𝑖 𝑗)) (shift (𝑆 (incPos 𝑖 (𝑖 + 𝑗))) (shift (𝑆 𝑖) t)))
    ≡⟨ ap Lam (shift² t (𝑆 𝑖) 𝑗) ⟩
  Lam (shift (𝑆 (shiftPos (𝑖 + 𝑗) 𝑖)) (shift (𝑆 (𝑖 + 𝑗)) t))
    ∎
shift² (App {Γ} {A} {B} t s) 𝑖 𝑗 =
  tr (λ Σ → Tm Σ B) (insertCtx² 𝑖 𝑗)
    (App (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t)) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 s)))
    ≡⟨ trApp (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t))
      (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 s)) ⟩
  App (tr (λ Σ → Tm Σ (A ⇒ B)) (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t)))
    (tr (λ Σ → Tm Σ A) (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 s)))
    ≡⟨ ap (App (tr (λ Σ → Tm Σ (A ⇒ B)) (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t))))
      (shift² s 𝑖 𝑗) ⟩
  App (tr (λ Σ → Tm Σ (A ⇒ B)) (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t)))
    (shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) s))
    ≡⟨ ap (λ x → App x (shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) s))) (shift² t 𝑖 𝑗) ⟩
  App (shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) t)) (shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) s))
    ∎

tr! : {Γ Δ : Ctx} (p : Γ ≡ Δ) → tr (λ Σ → Tms Σ ∅) p ! ≡ !
tr! refl = refl

tr⊕ : {Γ Δ Σ : Ctx} {A : Ty} (p : Γ ≡ Δ) (σ : Tms Γ Σ) (t : Tm Γ A) →
  tr (λ Ω → Tms Ω (Σ ⊹ A)) p (σ ⊕ t) ≡ tr (λ Ω → Tms Ω Σ) p σ ⊕ tr (λ Ω → Tm Ω A) p t
tr⊕ refl σ t = refl

shift²Tms : {Γ Δ : Ctx} {A B : Ty} (σ : Tms Γ Δ) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  tr (λ Σ → Tms Σ Δ) (insertCtx² {Γ} {A} {B} 𝑖 𝑗) (shiftTms (incPos 𝑖 (𝑖 + 𝑗)) (shiftTms 𝑖 σ))
    ≡ (shiftTms (shiftPos (𝑖 + 𝑗) 𝑖) (shiftTms (𝑖 + 𝑗) σ))
shift²Tms ! 𝑖 𝑗 = tr! (insertCtx² 𝑖 𝑗)
shift²Tms {Δ = Δ ⊹ A} (σ ⊕ t) 𝑖 𝑗 =
  tr (λ Σ → Tms Σ (Δ ⊹ A)) (insertCtx² 𝑖 𝑗) (shiftTms (incPos 𝑖 (𝑖 + 𝑗)) (shiftTms 𝑖 (σ ⊕ t)))
    ≡⟨ tr⊕ (insertCtx² 𝑖 𝑗) (map𝑇𝑚𝑠 (shift (incPos 𝑖 (𝑖 + 𝑗))) (map𝑇𝑚𝑠 (shift 𝑖) σ))
      (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t)) ⟩
  tr (λ Ω → Tms Ω Δ) (insertCtx² 𝑖 𝑗) (map𝑇𝑚𝑠 (shift (incPos 𝑖 (𝑖 + 𝑗))) (map𝑇𝑚𝑠 (shift 𝑖) σ))
    ⊕ tr (λ Ω → Tm Ω A) (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t))
    ≡⟨ ap (_⊕ tr (λ Ω → Tm Ω A) (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t)))
      (shift²Tms σ 𝑖 𝑗) ⟩
  shiftTms (shiftPos (𝑖 + 𝑗) 𝑖) (shiftTms (𝑖 + 𝑗) σ)
    ⊕ tr (λ Ω → Tm Ω A) (insertCtx² 𝑖 𝑗) (shift (incPos 𝑖 (𝑖 + 𝑗)) (shift 𝑖 t))
    ≡⟨ ap (shiftTms (shiftPos (𝑖 + 𝑗) 𝑖) (shiftTms (𝑖 + 𝑗) σ) ⊕_) (shift² t 𝑖 𝑗) ⟩
  shiftTms (shiftPos (𝑖 + 𝑗) 𝑖) (shiftTms (𝑖 + 𝑗) σ) ⊕ shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) t)
    ∎

deriveLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ A) (v : Var Δ B) →
  derive (insertTms 𝑖 σ s) (shiftVar 𝑖 v) ≡ derive σ v
deriveLem 𝑍 σ s v = refl
deriveLem (𝑆 𝑖) (σ ⊕ t) s 𝑧𝑣 = refl
deriveLem (𝑆 𝑖) (σ ⊕ t) s (𝑠𝑣 v) = deriveLem 𝑖 σ s v

deriveLem2 : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} (σ : Tms Γ Δ) (v : Var Δ B) →
  shift 𝑖 {A} (derive σ v) ≡ derive (shiftTms 𝑖 σ) v
deriveLem2 𝑖 (σ ⊕ t) 𝑧𝑣 = refl
deriveLem2 𝑖 (σ ⊕ t) (𝑠𝑣 v) = deriveLem2 𝑖 σ v

shiftInsertLem : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) (𝑗 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ B) →
  shiftTms 𝑖 {A} (insertTms 𝑗 σ s) ≡ insertTms 𝑗 (shiftTms 𝑖 σ) (shift 𝑖 s)
shiftInsertLem 𝑖 𝑍 σ s = refl
shiftInsertLem 𝑖 (𝑆 𝑗) (σ ⊕ t) s = ap (_⊕ shift 𝑖 t) (shiftInsertLem 𝑖 𝑗 σ s)

W₁InsertLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ B) →
  W₁Tms A (insertTms 𝑖 σ s) ≡ insertTms 𝑖 (W₁Tms A σ) (W₁Tm A s)
W₁InsertLem 𝑖 σ s = shiftInsertLem 𝑍 𝑖 σ s

shiftLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  shift 𝑖 t [ insertTms 𝑖 σ s ] ≡ t [ σ ]
shiftLem 𝑖 (V v) σ s =
  deriveLem 𝑖 σ s v
shiftLem 𝑖 (Lam {Γ} {A} t) σ s =
  Lam (shift (𝑆 𝑖) t [ W₂Tms A (insertTms 𝑖 σ s) ])
    ≡⟨ ap (λ x → Lam (shift (𝑆 𝑖) t [ x ⊕ 𝑧 ])) (W₁InsertLem 𝑖 σ s) ⟩
  Lam (shift (𝑆 𝑖) t [ insertTms (𝑆 𝑖) (W₂Tms A σ) (W₁Tm A s) ])
    ≡⟨ ap Lam (shiftLem (𝑆 𝑖) t (W₂Tms A σ) (W₁Tm A s) ) ⟩
  Lam (t [ W₂Tms A σ ])
    ∎
shiftLem 𝑖 (App t₁ t₂) σ s =
  App (shift 𝑖 t₁ [ insertTms 𝑖 σ s ]) (shift 𝑖 t₂ [ insertTms 𝑖 σ s ])
    ≡⟨ ap (App (shift 𝑖 t₁ [ insertTms 𝑖 σ s ])) (shiftLem 𝑖 t₂ σ s) ⟩
  App (shift 𝑖 t₁ [ insertTms 𝑖 σ s ]) (t₂ [ σ ])
    ≡⟨ ap (λ x → App x (t₂ [ σ ])) (shiftLem 𝑖 t₁ σ s) ⟩
  App (t₁ [ σ ]) (t₂ [ σ ])
    ∎

shift[] : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) →
  shift 𝑖 {A} (t [ σ ]) ≡ (t [ shiftTms 𝑖 σ ])
shift[] 𝑖 (V v) σ =
  deriveLem2 𝑖 σ v
shift[] 𝑖 (Lam {Γ} {A} t) σ =
  Lam (shift (𝑆 𝑖) (t [ W₂Tms A σ ]))
    ≡⟨ ap Lam (shift[] (𝑆 𝑖) t (W₂Tms A σ)) ⟩
  Lam (t [ shiftTms (𝑆 𝑖) (shiftTms 𝑍 σ) ⊕ 𝑧 ])
    ≡⟨ ap (λ x → Lam (t [ x ⊕ 𝑧 ])) (shift²Tms σ 𝑍 𝑖) ⟩
  Lam (t [ W₂Tms A (shiftTms 𝑖 σ) ])
    ∎
shift[] 𝑖 (App t s) σ =
  App (shift 𝑖 (t [ σ ])) (shift 𝑖 (s [ σ ]))
    ≡⟨ ap (App (shift 𝑖 (t [ σ ]))) (shift[] 𝑖 s σ) ⟩
  App (shift 𝑖 (t [ σ ])) (s [ shiftTms 𝑖 σ ])
    ≡⟨ ap (λ x → App x (s [ shiftTms 𝑖 σ ])) (shift[] 𝑖 t σ) ⟩
  App (t [ shiftTms 𝑖 σ ]) (s [ shiftTms 𝑖 σ ])
    ∎

Vlem0 : {Γ Δ : Ctx} {A : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  V (v [ σ ]𝑅) ≡ (V v) [ varify σ ]
Vlem0 𝑧𝑣 (σ ⊕ w) = refl
Vlem0 (𝑠𝑣 v) (σ ⊕ w) = Vlem0 v σ

Vlem1 : {Γ Δ Σ : Ctx} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  varify (σ ∘𝑅𝑒𝑛 τ) ≡ varify σ ∘Tms varify τ
Vlem1 ! τ = refl
Vlem1 (σ ⊕ v) τ =
  varify (σ ∘𝑅𝑒𝑛 τ) ⊕ V (v [ τ ]𝑅)
    ≡⟨ ap (varify (σ ∘𝑅𝑒𝑛 τ) ⊕_) (Vlem0 v τ) ⟩
  varify (σ ∘𝑅𝑒𝑛 τ) ⊕ V v [ varify τ ]
    ≡⟨ ap (_⊕ V v [ varify τ ]) (Vlem1 σ τ) ⟩
  varify (σ ⊕ v) ∘Tms varify τ
    ∎

Vlem2 : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
  varify (W₁𝑅𝑒𝑛 A σ) ≡ W₁Tms A (varify σ)
Vlem2 ! = refl
Vlem2 (σ ⊕ v) = ap (_⊕ V (𝑠𝑣 v)) (Vlem2 σ)

Vlem2' : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A : Ty} (σ : Ren Γ Δ) →
  varify (shiftRen 𝑖 {A} σ) ≡ shiftTms 𝑖 (varify σ)
Vlem2' 𝑖 ! = refl
Vlem2' 𝑖 (σ ⊕ v) = ap (_⊕ V (shiftVar 𝑖 v)) (Vlem2' 𝑖 σ)

Vlem3 : {Γ : Ctx} {A : Ty} → W₂Tms A (idTms Γ) ≡ idTms (Γ ⊹ A)
Vlem3 {Γ} = ap (_⊕ V 𝑧𝑣) (Vlem2 (id𝑅𝑒𝑛 Γ) ⁻¹)
    
Wlem0 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  W₁Tm A t [ σ ⊕ s ] ≡ t [ σ ]
Wlem0 t σ s = shiftLem 𝑍 t σ s

Wlem1 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  W₁Tms A σ ∘Tms (τ ⊕ t) ≡ σ ∘Tms τ
Wlem1 ! τ t = refl
Wlem1 {A = A} (σ ⊕ s) τ t =
  W₁Tms A σ ∘Tms (τ ⊕ t) ⊕ W₁Tm A s [ τ ⊕ t ]
    ≡⟨ ap (W₁Tms A σ ∘Tms (τ ⊕ t) ⊕_) (Wlem0 s τ t) ⟩
  W₁Tms A σ ∘Tms (τ ⊕ t) ⊕ s [ τ ]
    ≡⟨ ap (_⊕ s [ τ ]) (Wlem1 σ τ t) ⟩
  σ ⊕ s ∘Tms τ
    ∎

Wlem2 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  σ ∘Tms W₁Tms A τ ≡ W₁Tms A (σ ∘Tms τ)
Wlem2 ! τ = refl
Wlem2 {A = A} (σ ⊕ t) τ =
  σ ∘Tms W₁Tms A τ ⊕ t [ W₁Tms A τ ]
    ≡⟨ ap (σ ∘Tms W₁Tms A τ ⊕_) (shift[] 𝑍 t τ ⁻¹) ⟩
   σ ∘Tms W₁Tms A τ ⊕ W₁Tm A (t [ τ ])
     ≡⟨ ap (_⊕ W₁Tm A (t [ τ ])) (Wlem2 σ τ) ⟩
   W₁Tms A (σ ⊕ t ∘Tms τ)
    ∎

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
Wlem4 σ τ = ap (_⊕ 𝑧) (Wlem3 σ τ)

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
    ≡⟨ ap (λ x → Lam (t [ x ])) (Wlem4 σ τ) ⟩
  Lam (t [ W₂Tms A (σ ∘Tms τ) ])
    ∎
[][] (App t s) σ τ =
  App (t [ σ ] [ τ ]) (s [ σ ] [ τ ])
    ≡⟨ ap (App (t [ σ ] [ τ ])) ([][] s σ τ ) ⟩
  App (t [ σ ] [ τ ]) (s [ σ ∘Tms τ ])
    ≡⟨ ap (λ x → App x (s [ σ ∘Tms τ ])) ([][] t σ τ ) ⟩
  App (t [ σ ∘Tms τ ]) (s [ σ ∘Tms τ ])
    ∎

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
∘TmsIdR {Γ} (σ ⊕ t) =
  σ ∘Tms idTms Γ ⊕ t [ idTms Γ ]
    ≡⟨ ap (σ ∘Tms idTms Γ ⊕_) ([id] t) ⟩
  σ ∘Tms idTms Γ ⊕ t
    ≡⟨ ap (_⊕ t) (∘TmsIdR σ) ⟩
  σ ⊕ t
    ∎

[id] (V v) = deriveId v
[id] (Lam {Γ} {A} t) =
  Lam (t [ W₂Tms A (idTms Γ) ])
    ≡⟨ ap (λ x → Lam (t [ x ])) Vlem3 ⟩
  Lam (t [ idTms (Γ ⊹ A) ])
    ≡⟨ ap Lam ([id] t) ⟩
  Lam t
    ∎
[id] {Γ} (App t s) =
  App (t [ idTms Γ ]) (s [ idTms Γ ])
    ≡⟨ ap (App (t [ idTms Γ ])) ([id] s) ⟩
  App (t [ idTms Γ ]) s
    ≡⟨ ap (λ x → App x s) ([id] t) ⟩
  App t s
    ∎

Wlem1Varify : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  varify (W₁𝑅𝑒𝑛 A σ) ∘Tms (τ ⊕ t) ≡ (varify σ) ∘Tms τ
Wlem1Varify ! τ t = refl
Wlem1Varify {A = A} (σ ⊕ v) τ t = ap (_⊕ V v [ τ ]) (Wlem1Varify σ τ t)

∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms Δ ∘Tms σ ≡ σ
∘TmsIdL ! = refl
∘TmsIdL {Γ} {Δ ⊹ B} (σ ⊕ t) =
  varify (W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Δ)) ∘Tms (σ ⊕ t) ⊕ t
    ≡⟨ ap (_⊕ t) (Wlem1Varify (id𝑅𝑒𝑛 Δ) σ t) ⟩
  varify (id𝑅𝑒𝑛 Δ) ∘Tms σ ⊕ t
    ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
  σ ⊕ t
    ∎

Wlem5 : {Γ : Ctx} {A B : Ty} (t : Tm Γ B) →
  t [ π ] ≡ W₁Tm A t
Wlem5 {Γ} {A} t =
  t [ π ]
    ≡⟨ ap (t [_]) (Vlem2 (id𝑅𝑒𝑛 Γ)) ⟩
  t [ W₁Tms A (idTms Γ) ]
    ≡⟨ shift[] 𝑍 t (idTms Γ) ⁻¹ ⟩
  W₁Tm A (t [ idTms Γ ])
    ≡⟨ ap (W₁Tm A) ([id] t) ⟩
  W₁Tm A t
    ∎

Wlem6 : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) →
  σ ∘Tms π ≡ W₁Tms A σ
Wlem6 {Γ} {Δ} {A} σ =
  σ ∘Tms π
    ≡⟨ ap (σ ∘Tms_) (Vlem2 (id𝑅𝑒𝑛 Γ)) ⟩
  σ ∘Tms W₁Tms A (idTms Γ)
    ≡⟨ Wlem2 σ (idTms Γ) ⟩
  W₁Tms A (σ ∘Tms idTms Γ)
    ≡⟨ ap (W₁Tms A) (∘TmsIdR σ) ⟩
  W₁Tms A σ
    ∎

idInsertLem : (Γ : Ctx) (A : Ty) (𝑖 : CtxPos Γ) →
  idTms (insertCtx Γ A 𝑖) ≡ insertTms 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))
idInsertLem Γ A 𝑍 = ap (_⊕ V 𝑧𝑣) (Vlem2 (id𝑅𝑒𝑛 Γ))
idInsertLem (Γ ⊹ B) A (𝑆 𝑖) =
  idTms (insertCtx Γ A 𝑖 ⊹ B)
    ≡⟨ ap (_⊕ V 𝑧𝑣 )(Vlem2 (id𝑅𝑒𝑛 (insertCtx Γ A 𝑖))) ⟩
  W₁Tms B (idTms (insertCtx Γ A 𝑖)) ⊕ V 𝑧𝑣
    ≡⟨ ap (λ x → W₁Tms B x ⊕ V 𝑧𝑣) (idInsertLem Γ A 𝑖) ⟩
  W₁Tms B (insertTms 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ ap (_⊕ V 𝑧𝑣) (W₁InsertLem 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))) ⟩
  insertTms 𝑖 (W₁Tms B (shiftTms 𝑖 (idTms Γ))) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ ap (λ x → insertTms 𝑖 x (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣)
      (shift²Tms (idTms Γ) 𝑍 𝑖 ⁻¹) ⟩
  insertTms 𝑖 (shiftTms (𝑆 𝑖) (W₁Tms B (idTms Γ))) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ ap (λ x → insertTms 𝑖 (shiftTms (𝑆 𝑖) x) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣)
      (Vlem2 (id𝑅𝑒𝑛 Γ) ⁻¹) ⟩
  insertTms (𝑆 𝑖) (shiftTms (𝑆 𝑖) (idTms (Γ ⊹ B))) (V (varToInsertion (Γ ⊹ B) A (𝑆 𝑖)))
    ∎
