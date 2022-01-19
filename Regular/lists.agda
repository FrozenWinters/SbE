module lists where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Relation.Binary.PropositionalEquality
  renaming (cong to ap; sym to _⁻¹; subst to tr) hiding ([_]) public
open ≡-Reasoning public
open import Function public

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

-- We define the basic data structures used to build contextual categories.

-- 𝐶𝑡𝑥 is a (reversed) list former
infixl 20 _⊹_
data 𝐶𝑡𝑥 (ty : Type ℓ) : Type ℓ where
  ∅ : 𝐶𝑡𝑥 ty
  _⊹_ : 𝐶𝑡𝑥 ty → ty → 𝐶𝑡𝑥 ty

map𝐶𝑡𝑥 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : 𝐶𝑡𝑥 ty₁) → 𝐶𝑡𝑥 ty₂
map𝐶𝑡𝑥 f ∅ = ∅
map𝐶𝑡𝑥 f (Γ ⊹ A) = map𝐶𝑡𝑥 f Γ ⊹ f A

-- 𝑇𝑚𝑠 forms indexed lists representing substitutions (terms of given types in a common context)
infixl 20 _⊕_
data 𝑇𝑚𝑠 {ty : Type ℓ₁} (tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂)
     : (Γ Δ : 𝐶𝑡𝑥 ty) → Type (ℓ₁ ⊔ ℓ₂) where
  ! : {Γ : 𝐶𝑡𝑥 ty} → 𝑇𝑚𝑠 tm Γ ∅
  _⊕_ : {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑇𝑚𝑠 tm Γ Δ → tm Γ A → 𝑇𝑚𝑠 tm Γ (Δ ⊹ A)

map𝑇𝑚𝑠 : {ty : Type ℓ₁} {Γ₁ Γ₂ Δ : 𝐶𝑡𝑥 ty} {tm₁ : 𝐶𝑡𝑥 ty → ty → Type ℓ₂}
  {tm₂ : 𝐶𝑡𝑥 ty → ty → Type ℓ₃} (f : {A : ty} → tm₁ Γ₁ A → tm₂ Γ₂ A)
  (σ : 𝑇𝑚𝑠 tm₁ Γ₁ Δ) → 𝑇𝑚𝑠 tm₂ Γ₂ Δ
map𝑇𝑚𝑠 f ! = !
map𝑇𝑚𝑠 f (σ ⊕ t) = map𝑇𝑚𝑠 f σ ⊕ f t

{-prove𝑇𝑚𝑠 : {ty : Type ℓ₁} {Γ₁ Γ₂ Δ : 𝐶𝑡𝑥 ty} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂}
  {f g : {A : ty} → tm Γ₁ A → tm Γ₂ A} (p : {A : ty} (t : tm Γ₁ A) → f t ≡ g t)
  (σ : 𝑇𝑚𝑠 tm Γ₁ Δ) → map𝑇𝑚𝑠 {tm₂ = tm} f σ ≡ map𝑇𝑚𝑠 g σ
prove𝑇𝑚𝑠 p ! = refl
prove𝑇𝑚𝑠 {f = f} {g} p (σ ⊕ t) =
  map𝑇𝑚𝑠 f σ ⊕ f t
    ≡⟨ ap (map𝑇𝑚𝑠 f σ ⊕_) (p t) ⟩
  map𝑇𝑚𝑠 f σ ⊕ g t
    ≡⟨ ap (_⊕ g t) (prove𝑇𝑚𝑠 p σ) ⟩
  map𝑇𝑚𝑠 g σ ⊕ g t
    ∎-}

π𝑇𝑚𝑠 : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty}
  → 𝑇𝑚𝑠 tm Γ (Δ ⊹ A) → 𝑇𝑚𝑠 tm Γ Δ
π𝑇𝑚𝑠 (σ ⊕ t) = σ

𝑧𝑇𝑚𝑠 : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty}
  → 𝑇𝑚𝑠 tm Γ (Δ ⊹ A) → tm Γ A
𝑧𝑇𝑚𝑠 (σ ⊕ t) = t

map𝑇𝑚𝑠comp : {ty : Type ℓ₁} {tm₁ : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {tm₂ : 𝐶𝑡𝑥 ty → ty → Type ℓ₃}
  {tm₃ : 𝐶𝑡𝑥 ty → ty → Type ℓ₄} {Γ₁ Γ₂ Γ₃ Δ : 𝐶𝑡𝑥 ty} (f : {A : ty} → tm₂ Γ₂ A → tm₃ Γ₃ A)
  (g : {A : ty} → tm₁ Γ₁ A → tm₂ Γ₂ A) (σ : 𝑇𝑚𝑠 tm₁ Γ₁ Δ) →
  map𝑇𝑚𝑠 {tm₁ = tm₂} {tm₂ = tm₃} f (map𝑇𝑚𝑠 g σ) ≡ map𝑇𝑚𝑠 (f ∘ g) σ
map𝑇𝑚𝑠comp f g ! = refl
map𝑇𝑚𝑠comp {tm₂ = tm₂} {Γ₂ = Γ₂} f g (σ ⊕ t) = ap (_⊕ f (g t)) (map𝑇𝑚𝑠comp f g σ)

-- Variables
data 𝑉𝑎𝑟 (ty : Type ℓ) : (Γ : 𝐶𝑡𝑥 ty) (A : ty) → Type ℓ where
  𝑧𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑉𝑎𝑟 ty (Γ ⊹ A) A
  𝑠𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A B : ty} → 𝑉𝑎𝑟 ty Γ A → 𝑉𝑎𝑟 ty (Γ ⊹ B) A

𝑅𝑒𝑛 : (ty : Type ℓ) → 𝐶𝑡𝑥 ty → 𝐶𝑡𝑥 ty → Type ℓ
𝑅𝑒𝑛 ty = 𝑇𝑚𝑠 (𝑉𝑎𝑟 ty)

module _ {ty : Type ℓ} where
  private
    ctx = 𝐶𝑡𝑥 ty
    ren = 𝑅𝑒𝑛 ty
    var = 𝑉𝑎𝑟 ty
  
  W₁𝑅𝑒𝑛 : {Γ Δ : ctx} (A : ty) → ren Γ Δ → ren (Γ ⊹ A) Δ
  W₁𝑅𝑒𝑛 A = map𝑇𝑚𝑠 𝑠𝑣

  W₂𝑅𝑒𝑛 : {Γ Δ : ctx} (A : ty) → ren Γ Δ → ren (Γ ⊹ A) (Δ ⊹ A)
  W₂𝑅𝑒𝑛 A σ = W₁𝑅𝑒𝑛 A σ ⊕ 𝑧𝑣

  id𝑅𝑒𝑛 : (Γ : ctx) → ren Γ Γ
  id𝑅𝑒𝑛 ∅ = !
  id𝑅𝑒𝑛 (Γ ⊹ A) = W₂𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)

  infix 30 _[_]𝑅
  _[_]𝑅 : {Γ Δ : ctx} {A : ty} → var Δ A → ren Γ Δ → var Γ A
  𝑧𝑣 [ σ ⊕ v ]𝑅 = v
  𝑠𝑣 v [ σ ⊕ w ]𝑅 = v [ σ ]𝑅

  infixl 30 _∘𝑅𝑒𝑛_
  _∘𝑅𝑒𝑛_ : {Γ Δ Σ : ctx} → ren Δ Σ → ren Γ Δ → ren Γ Σ
  σ ∘𝑅𝑒𝑛 τ = map𝑇𝑚𝑠 _[ τ ]𝑅 σ

  Wlem1𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) (v : var Γ A) →
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 (τ ⊕ v) ≡ σ ∘𝑅𝑒𝑛 τ
  Wlem1𝑅𝑒𝑛 ! τ v = refl
  Wlem1𝑅𝑒𝑛 (σ ⊕ w) τ v = ap (_⊕ w [ τ ]𝑅) (Wlem1𝑅𝑒𝑛 σ τ v)

  Wlem2𝑅𝑒𝑛 : {Γ Δ : ctx} {A B : ty} (v : var Δ A) (σ : ren Γ Δ) →
    v [ W₁𝑅𝑒𝑛 B σ ]𝑅 ≡ 𝑠𝑣 (v [ σ ]𝑅)
  Wlem2𝑅𝑒𝑛 𝑧𝑣 (σ ⊕ v) = refl
  Wlem2𝑅𝑒𝑛 (𝑠𝑣 v) (σ ⊕ w) = Wlem2𝑅𝑒𝑛 v σ

  Wlem3𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) →
    σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ≡ W₁𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ)
  Wlem3𝑅𝑒𝑛 ! τ = refl
  Wlem3𝑅𝑒𝑛 {A = A} (σ ⊕ v) τ =
    σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ⊕ v [ W₁𝑅𝑒𝑛 A τ ]𝑅
      ≡⟨ ap (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ⊕_) (Wlem2𝑅𝑒𝑛 v τ) ⟩
    σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ⊕ 𝑠𝑣 (v [ τ ]𝑅)
      ≡⟨ ap (_⊕ 𝑠𝑣 (v [ τ ]𝑅)) (Wlem3𝑅𝑒𝑛 σ τ) ⟩
    W₁𝑅𝑒𝑛 A ((σ ⊕ v) ∘𝑅𝑒𝑛 τ)
      ∎

  Wlem4𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) →
    W₂𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ≡ W₂𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ)
  Wlem4𝑅𝑒𝑛 ! τ = refl
  Wlem4𝑅𝑒𝑛 {A = A} (σ ⊕ v) τ =
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 (W₁𝑅𝑒𝑛 A τ ⊕ 𝑧𝑣) ⊕ v [ W₁𝑅𝑒𝑛 A τ ]𝑅 ⊕ 𝑧𝑣
      ≡⟨ ap (λ x → x ⊕ v [ W₁𝑅𝑒𝑛 A τ ]𝑅 ⊕ 𝑧𝑣) (Wlem1𝑅𝑒𝑛 σ (W₁𝑅𝑒𝑛 A τ) 𝑧𝑣) ⟩
    σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ⊕ v [ W₁𝑅𝑒𝑛 A τ ]𝑅 ⊕ 𝑧𝑣
      ≡⟨ ap (λ x → σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ⊕ x ⊕ 𝑧𝑣) (Wlem2𝑅𝑒𝑛 v τ) ⟩
    σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ⊕ 𝑠𝑣 (v [ τ ]𝑅) ⊕ 𝑧𝑣
      ≡⟨ ap (λ x → x ⊕ 𝑠𝑣 (v [ τ ]𝑅) ⊕ 𝑧𝑣) (Wlem3𝑅𝑒𝑛 σ τ) ⟩
    W₂𝑅𝑒𝑛 A ((σ ⊕ v) ∘𝑅𝑒𝑛 τ)
      ∎

  Wlem5𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) →
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ≡ W₁𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ)
  Wlem5𝑅𝑒𝑛 ! τ = refl
  Wlem5𝑅𝑒𝑛 {A = A} (σ ⊕ v) τ =
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ⊕ v [ W₁𝑅𝑒𝑛 A τ ]𝑅
      ≡⟨ ap (W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ⊕_) (Wlem2𝑅𝑒𝑛 v τ) ⟩
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ⊕ 𝑠𝑣 (v [ τ ]𝑅)
      ≡⟨ ap (_⊕ 𝑠𝑣 (v [ τ ]𝑅)) (Wlem5𝑅𝑒𝑛 σ τ) ⟩
    W₁𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ) ⊕ 𝑠𝑣 (v [ τ ]𝑅)
      ∎

  [][]𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (v : var Σ A) (σ : ren Δ Σ) (τ : ren Γ Δ) →
    v [ σ ]𝑅 [ τ ]𝑅 ≡ v [ σ ∘𝑅𝑒𝑛 τ ]𝑅
  [][]𝑅𝑒𝑛 𝑧𝑣 (σ ⊕ v) τ = refl
  [][]𝑅𝑒𝑛 (𝑠𝑣 v) (σ ⊕ w) τ = [][]𝑅𝑒𝑛 v σ τ

  ∘𝑅𝑒𝑛Assoc : {Γ Δ Σ Ω : ctx} (σ : ren Σ Ω) (τ : ren Δ Σ) (μ : ren Γ Δ) →
    σ ∘𝑅𝑒𝑛 τ ∘𝑅𝑒𝑛 μ ≡ σ ∘𝑅𝑒𝑛 (τ ∘𝑅𝑒𝑛 μ)
  ∘𝑅𝑒𝑛Assoc ! τ μ = refl
  ∘𝑅𝑒𝑛Assoc (σ ⊕ v) τ μ =
    σ ∘𝑅𝑒𝑛 τ ∘𝑅𝑒𝑛 μ ⊕ v [ τ ]𝑅 [ μ ]𝑅
      ≡⟨ ap (σ ∘𝑅𝑒𝑛 τ ∘𝑅𝑒𝑛 μ ⊕_) ([][]𝑅𝑒𝑛 v τ μ) ⟩
    σ ∘𝑅𝑒𝑛 τ ∘𝑅𝑒𝑛 μ ⊕ v [ τ ∘𝑅𝑒𝑛 μ ]𝑅
      ≡⟨ ap (_⊕ v [ τ ∘𝑅𝑒𝑛 μ ]𝑅) (∘𝑅𝑒𝑛Assoc σ τ μ) ⟩
    σ ∘𝑅𝑒𝑛 (τ ∘𝑅𝑒𝑛 μ) ⊕ v [ τ ∘𝑅𝑒𝑛 μ ]𝑅
      ∎

  ∘𝑅𝑒𝑛IdL : {Γ Δ : ctx} (σ : ren Γ Δ) → id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ ≡ σ
  ∘𝑅𝑒𝑛IdL ! = refl
  ∘𝑅𝑒𝑛IdL {Γ} {Δ ⊹ A} (σ ⊕ v) =
    W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 (σ ⊕ v) ⊕ v
      ≡⟨ ap (_⊕ v) (Wlem1𝑅𝑒𝑛 (id𝑅𝑒𝑛 Δ) σ v) ⟩
    id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ ⊕ v
      ≡⟨ ap (_⊕ v) (∘𝑅𝑒𝑛IdL σ) ⟩
    σ ⊕ v
      ∎

  [id]𝑅𝑒𝑛 : {Γ : ctx} {A : ty} (v : var Γ A) →
    v [ id𝑅𝑒𝑛 Γ ]𝑅 ≡ v
  [id]𝑅𝑒𝑛 𝑧𝑣 = refl
  [id]𝑅𝑒𝑛 {Γ ⊹ B} {A} (𝑠𝑣 v) =
    v [ W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Γ) ]𝑅
      ≡⟨ Wlem2𝑅𝑒𝑛 v (id𝑅𝑒𝑛 Γ) ⟩
    𝑠𝑣 (v [ id𝑅𝑒𝑛 Γ ]𝑅)
      ≡⟨ ap 𝑠𝑣 ([id]𝑅𝑒𝑛 v) ⟩
    𝑠𝑣 v
      ∎

  ∘𝑅𝑒𝑛IdR : {Γ Δ : ctx} (σ : ren Γ Δ) → σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Γ ≡ σ
  ∘𝑅𝑒𝑛IdR ! = refl
  ∘𝑅𝑒𝑛IdR {Γ} (σ ⊕ v) =
    σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Γ ⊕ v [ id𝑅𝑒𝑛 Γ ]𝑅
      ≡⟨ ap (σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Γ ⊕_) ([id]𝑅𝑒𝑛 v) ⟩
    σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Γ ⊕ v
      ≡⟨ ap (_⊕ v) (∘𝑅𝑒𝑛IdR σ) ⟩
    σ ⊕ v
      ∎

derive : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty} →
  𝑇𝑚𝑠 tm Γ Δ → 𝑉𝑎𝑟 ty Δ A → tm Γ A
derive σ 𝑧𝑣 = 𝑧𝑇𝑚𝑠 σ
derive σ (𝑠𝑣 v) = derive (π𝑇𝑚𝑠 σ) v

deriveMap : {ty : Type ℓ₁} {tm₁ : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {tm₂ : 𝐶𝑡𝑥 ty → ty → Type ℓ₃}
  {Γ Δ Σ : 𝐶𝑡𝑥 ty} (f : {A : ty} → tm₁ Γ A → tm₂ Δ A) (σ : 𝑇𝑚𝑠 tm₁ Γ Σ) {A : ty}
  (v : 𝑉𝑎𝑟 ty Σ A) → derive (map𝑇𝑚𝑠 {tm₁ = tm₁} {tm₂} f σ) v ≡ f (derive σ v)
deriveMap f (σ ⊕ t) 𝑧𝑣 = refl
deriveMap f (σ ⊕ t) (𝑠𝑣 v) = deriveMap f σ v
