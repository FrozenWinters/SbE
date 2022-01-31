module norm where

open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public

open import lists
open import syn
open import normal
open import trace

data ⊤ : Type lzero where
  tt : ⊤

-- We bootstrap the definition of the semantic presheaves

Element : Ctx → Ty → Set
infix 30 _[_]𝐸𝑙
_≡𝐸𝑙_ : {Γ : Ctx} {A : Ty} (𝓈 𝓉 : Element Γ A) → Type lzero
_[_]𝐸𝑙 : {Γ Δ : Ctx} {A : Ty} → Element Δ A → Ren Γ Δ → Element Γ A

{-# NO_POSITIVITY_CHECK #-}
record Element⇒ (Γ : Ctx) (A B : Ty) : Set where
  inductive
  constructor El
  field
    ob : {Δ : Ctx} → Ren Δ Γ → Element Δ A → Element Δ B
    ext : {Δ : Ctx} (σ : Ren Δ Γ) {𝓈 𝓉 : Element Δ A} → 𝓈 ≡𝐸𝑙 𝓉 → ob σ 𝓈 ≡𝐸𝑙 ob σ 𝓉
    hom : {Δ Σ : Ctx} (σ : Ren Δ Γ) (𝓈 : Element Δ A) (τ : Ren Σ Δ) →
      ob σ 𝓈 [ τ ]𝐸𝑙 ≡𝐸𝑙 ob (σ ∘𝑅𝑒𝑛 τ) (𝓈 [ τ ]𝐸𝑙)

Element Γ (Base X) = Nf Γ (Base X)
Element Γ (A ⇒ B) = Element⇒ Γ A B

open Element⇒

_≡𝐸𝑙_ {Γ} {Base c} N M = N ≡ M
_≡𝐸𝑙_ {Γ} {A ⇒ B} 𝒻 ℊ = {Δ : Ctx} (σ : Ren Δ Γ) (𝓈 : Element Δ A) → ob 𝒻 σ 𝓈 ≡𝐸𝑙 ob ℊ σ 𝓈

infixl 30 _∙𝐸𝑙_
_∙𝐸𝑙_ : {Γ : Ctx} {A : Ty} {𝓈 𝓉 𝓊 : Element Γ A} → 𝓈 ≡𝐸𝑙 𝓉 → 𝓉 ≡𝐸𝑙 𝓊 → 𝓈 ≡𝐸𝑙 𝓊
_∙𝐸𝑙_ {A = Base c} a b = a ∙ b
_∙𝐸𝑙_ {A = A ⇒ B} a b σ 𝓈 = a σ 𝓈 ∙𝐸𝑙 b σ 𝓈

infix 40 _⁻¹𝐸𝑙
_⁻¹𝐸𝑙 : {Γ : Ctx} {A : Ty} {𝓈 𝓉 : Element Γ A} → 𝓈 ≡𝐸𝑙 𝓉 → 𝓉 ≡𝐸𝑙 𝓈
_⁻¹𝐸𝑙 {A = Base c} a = a ⁻¹
_⁻¹𝐸𝑙 {A = A ⇒ B} a σ 𝓈 = a σ 𝓈 ⁻¹𝐸𝑙

refl𝐸𝑙 : {Γ : Ctx} {A : Ty} {𝓈 : Element Γ A} → 𝓈 ≡𝐸𝑙 𝓈
refl𝐸𝑙 {A = Base c} = refl
refl𝐸𝑙 {A = A ⇒ B} σ 𝓈 = refl𝐸𝑙

⟪_⟫ : {Γ : Ctx} {A : Ty} {𝓈 𝓉 : Element Γ A} → 𝓈 ≡ 𝓉 → 𝓈 ≡𝐸𝑙 𝓉
⟪ refl ⟫ = refl𝐸𝑙

_[_]𝐸𝑙 {A = Base x} 𝓈 σ = 𝓈 [ σ ]NF
_[_]𝐸𝑙 {A = A ⇒ B} 𝒻 σ =
  El
    (λ τ 𝓈 → ob 𝒻 (σ ∘𝑅𝑒𝑛 τ) 𝓈)
    (λ τ a → ext 𝒻 (σ ∘𝑅𝑒𝑛 τ) a)
    (λ τ 𝓈 μ →
      hom 𝒻 (σ ∘𝑅𝑒𝑛 τ) 𝓈 μ ∙𝐸𝑙 ⟪ ap (λ x → ob 𝒻 x (𝓈 [ μ ]𝐸𝑙)) (∘𝑅𝑒𝑛Assoc σ τ μ) ⟫)

[id]𝐸𝑙 : {Γ : Ctx} {A : Ty} (𝓈 : Element Γ A) → 𝓈 [ id𝑅𝑒𝑛 Γ ]𝐸𝑙 ≡𝐸𝑙 𝓈
[id]𝐸𝑙 {Γ} {Base c} N = [id]NF N
[id]𝐸𝑙 {Γ} {A ⇒ B} 𝒻 σ 𝓈 = ⟪ ap (λ x → ob 𝒻 x 𝓈) (∘𝑅𝑒𝑛IdL σ) ⟫

[][]𝐸𝑙 : {Γ Δ Σ : Ctx} {A : Ty} (𝓈 : Element Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  𝓈 [ σ ]𝐸𝑙 [ τ ]𝐸𝑙 ≡𝐸𝑙 𝓈 [ σ ∘𝑅𝑒𝑛 τ ]𝐸𝑙
[][]𝐸𝑙 {A = Base c} N σ τ = [][]NF N σ τ
[][]𝐸𝑙 {A = A ⇒ B} 𝒻 σ τ μ 𝓈 = ⟪ ap (λ x → ob 𝒻 x 𝓈) (∘𝑅𝑒𝑛Assoc σ τ μ ⁻¹) ⟫

q : {Γ : Ctx} {A : Ty} → Element Γ A → Nf Γ A
u : {Γ : Ctx} {A : Ty} → Ne Γ A → Element Γ A

q-nat : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈 : Element Δ A) →
  q (𝓈 [ σ ]𝐸𝑙) ≡ q 𝓈 [ σ ]NF
u-nat : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (N : Ne Δ A) →
  u (N [ σ ]NE) ≡𝐸𝑙 u N [ σ ]𝐸𝑙

q {A = Base X} 𝓈 = 𝓈
q {Γ} {A ⇒ B} 𝒻 = LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))

q-ext : {Γ : Ctx} {A : Ty} {𝓈 𝓉 : Element Γ A} → 𝓈 ≡𝐸𝑙 𝓉 → q 𝓈 ≡ q 𝓉
q-ext {Γ} {Base c} a = a
q-ext {Γ} {A ⇒ B} a = ap LAM (q-ext (a (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))

u {A = Base X} M = NEU M
u {A = A ⇒ B} M =
  El
    (λ σ 𝓈 → u (APP (M [ σ ]NE) (q 𝓈)))
    (λ σ a → ⟪ ap (λ x → u (APP (M [ σ ]NE) x)) (q-ext a) ⟫)
    (λ σ 𝓈 τ →
      u-nat τ (APP (M [ σ ]NE) (q 𝓈)) ⁻¹𝐸𝑙
      ∙𝐸𝑙 ⟪ ap (λ x → u (APP x (q 𝓈 [ τ ]NF))) ([][]NE M σ τ) ⟫
      ∙𝐸𝑙 ⟪ ap (λ x → u (APP (M [ σ ∘𝑅𝑒𝑛 τ ]NE) x)) (q-nat τ 𝓈 ⁻¹) ⟫)

u-nat {Base x} σ N = refl
u-nat {A ⇒ B} σ N τ 𝓈 = ⟪ ap (λ x → u (APP x (q 𝓈))) ([][]NE N σ τ) ⟫

q-nat {Base x} σ 𝓈 = refl
q-nat {A ⇒ B} {Γ} {Δ} σ 𝒻 =
  LAM (q (ob 𝒻 (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))
    ≡⟨ ap LAM (q-ext (ext 𝒻 (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u-nat (W₂𝑅𝑒𝑛 A σ) (VN 𝑧𝑣)))) ⟩
  LAM (q (ob 𝒻 (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)))
    ≡⟨ ap (λ x → LAM (q (ob 𝒻 x (u (VN 𝑧𝑣) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)))) lem ⟩
  LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A σ) (u (VN 𝑧𝑣) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)))
    ≡⟨ ap LAM (q-ext (hom 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) (W₂𝑅𝑒𝑛 A σ)) ⁻¹) ⟩
  LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙))
    ≡⟨ ap LAM (q-nat (W₂𝑅𝑒𝑛 A σ) (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)))) ⟩
  LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣))) [ W₂𝑅𝑒𝑛 A σ ]NF)
    ∎ where
    lem : σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ≡ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 (W₂𝑅𝑒𝑛 A σ)
    lem =
      σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)
        ≡⟨ Wlem3𝑅𝑒𝑛 σ (id𝑅𝑒𝑛 Γ) ⟩
      W₁𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Γ)
        ≡⟨ ap (W₁𝑅𝑒𝑛 A) (∘𝑅𝑒𝑛IdR σ) ⟩
      W₁𝑅𝑒𝑛 A σ
        ≡⟨ ap (W₁𝑅𝑒𝑛 A) (∘𝑅𝑒𝑛IdL σ ⁻¹) ⟩
      W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ)
        ≡⟨ Wlem5𝑅𝑒𝑛 (id𝑅𝑒𝑛 Δ) σ ⁻¹ ⟩
      W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A σ
        ∎

comp : {Γ : Ctx} {A : Ty} (N : Ne Γ A) → Steps (ιNf (q (u N))) (ιNe N)
comp {A = Base s} N = []
comp {Γ} {A ⇒ B} N =
  deepens (𝐿 𝑂) (comp (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
    ⊙ deepens (𝐿 (𝐴₂ (ιNe (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE)) 𝑂)) (comp (VN 𝑧𝑣))
    ∷≡
      (Lam (App (ιNe (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE)) (V 𝑧𝑣))
        ≡⟨ ap (λ x → Lam (App x (V 𝑧𝑣))) (ιNeLem N (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ))) ⟩
      Lam (App (ιNe N [ π ]) (V 𝑧𝑣))
        ≡⟨ ap (λ x → Lam (App x (V 𝑧𝑣))) (Wlem5 (ιNe N)) ⟩
      Lam (App (W₁Tm A (ιNe N)) (V 𝑧𝑣))
        ∎)
    ∷ ⟨ 𝑂 ⊚ η (ιNe N) ⟩⁻¹

SafeType : {Γ : Ctx} {A : Ty} (𝓈 : Element Γ A) → Set

SafeElement : Ctx → Ty → Set
SafeElement Γ A = Σ (Element Γ A) SafeType

SafeType {Γ} {Base c} N = ⊤
SafeType {Γ} {A ⇒ B} 𝒻 =
  {Δ : Ctx} (σ : Ren Δ Γ) (𝓈 : SafeElement Δ A) →
    Steps (ιNf (q (ob 𝒻 σ (fst 𝓈)))) (App (ιNf (q 𝒻 [ σ ]NF)) (ιNf (q (fst 𝓈))))
      ×  SafeType (ob 𝒻 σ (fst 𝓈))

_[_]𝐸𝑙-safe : {Γ Δ : Ctx} {A : Ty} (𝓈 : SafeElement Δ A) (σ : Ren Γ Δ) →
  SafeType (fst 𝓈 [ σ ]𝐸𝑙)
_[_]𝐸𝑙-safe {A = Base c} 𝓈 σ = tt
_[_]𝐸𝑙-safe {A = A ⇒ B} 𝓈 σ τ 𝓉 =
  fst (snd 𝓈 (σ ∘𝑅𝑒𝑛 τ) 𝓉)
    ∷≡
      (App (ιNf (q (fst 𝓈) [ σ ∘𝑅𝑒𝑛 τ ]NF)) (ιNf (q (fst 𝓉)))
        ≡⟨ ap (λ x → App (ιNf x) (ιNf (q (fst 𝓉)))) ([][]NF (q (fst 𝓈)) σ τ ⁻¹) ⟩
      App (ιNf (q (fst 𝓈) [ σ ]NF [ τ ]NF)) (ιNf (q (fst 𝓉)))
        ≡⟨ ap (λ x → App (ιNf (x [ τ ]NF)) (ιNf (q (fst 𝓉)))) (q-nat σ (fst 𝓈) ⁻¹) ⟩
      App (ιNf (q (fst 𝓈 [ σ ]𝐸𝑙) [ τ ]NF)) (ιNf (q (fst 𝓉)))
        ∎ ) ,
    snd (snd 𝓈 (σ ∘𝑅𝑒𝑛 τ) 𝓉)

_[_]𝐸𝑙-S : {Γ Δ : Ctx} {A : Ty} → SafeElement Δ A → Ren Γ Δ → SafeElement Γ A
𝓈 [ σ ]𝐸𝑙-S = fst 𝓈 [ σ ]𝐸𝑙 , 𝓈 [ σ ]𝐸𝑙-safe

u-safe : {Γ : Ctx} {A : Ty} (N : Ne Γ A) → SafeType (u N)
u-safe {Γ} {Base c} N = tt
u-safe {Γ} {A ⇒ B} N σ 𝓈 =
  comp (APP (N [ σ ]NE) (q (fst 𝓈)))
    ∷≡ ap (λ x → (App x (ιNf (q (fst 𝓈))))) (ιNeLem N σ)
    ⊙ deepens (𝐴₁ 𝑂 (ιNf (q (fst 𝓈)))) (invertSteps (comp N) [ varify σ ]𝑆')
    ∷≡
      (App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
        [ W₂Tms A (varify σ) ])) (ιNf (q (fst 𝓈)))
        ≡⟨ ap (λ x → App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
          [ x ⊕ 𝑧 ])) (ιNf (q (fst 𝓈)))) (Vlem2 σ ⁻¹) ⟩
      App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
        [ varify (W₂𝑅𝑒𝑛 A σ) ])) (ιNf (q (fst 𝓈)))
        ≡⟨ ap (λ x → App (Lam x) (ιNf (q (fst 𝓈))))
          (ιNfLem (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))) (W₂𝑅𝑒𝑛 A σ) ⁻¹) ⟩
      App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
        [ W₂𝑅𝑒𝑛 A σ ]NF))) (ιNf (q (fst 𝓈)))
        ∎) ,
    u-safe (APP (N [ σ ]NE) (q (fst 𝓈)))

u-S : {Γ : Ctx} {A : Ty} → Ne Γ A → SafeElement Γ A
u-S N = u N , u-safe N

Elements = 𝑇𝑚𝑠 Element
SafeElements = 𝑇𝑚𝑠 SafeElement

_≡𝐸𝑙𝑠_ : {Γ Δ : Ctx} (𝓈s 𝓉s : Elements Γ Δ) → Type lzero
! ≡𝐸𝑙𝑠 ! = ⊤
(𝓈s ⊕ 𝓈) ≡𝐸𝑙𝑠 (𝓉s ⊕ 𝓉) = 𝓈s ≡𝐸𝑙𝑠 𝓉s × 𝓈 ≡𝐸𝑙 𝓉

refl𝐸𝑙𝑠 : {Γ Δ : Ctx} {𝓈s : Elements Γ Δ} → 𝓈s ≡𝐸𝑙𝑠 𝓈s
refl𝐸𝑙𝑠 {𝓈s = !} = tt
refl𝐸𝑙𝑠 {𝓈s = 𝓈s ⊕ 𝓈} = refl𝐸𝑙𝑠 , refl𝐸𝑙

infix 40 _⁻¹𝐸𝑙𝑠
_⁻¹𝐸𝑙𝑠 : {Γ Δ : Ctx} {𝓈s 𝓉s : Elements Γ Δ} → 𝓈s ≡𝐸𝑙𝑠 𝓉s → 𝓉s ≡𝐸𝑙𝑠 𝓈s
_⁻¹𝐸𝑙𝑠 {𝓈s = !} { ! } as = tt
_⁻¹𝐸𝑙𝑠 {𝓈s = 𝓈s ⊕ 𝓈} {𝓉s ⊕ 𝓉} (as , a) = as ⁻¹𝐸𝑙𝑠 , a ⁻¹𝐸𝑙

infix 30 _[_]𝐸𝑙𝑠
_[_]𝐸𝑙𝑠 : {Γ Δ Σ : Ctx} → Elements Δ Σ → Ren Γ Δ → Elements Γ Σ
𝓈s [ σ ]𝐸𝑙𝑠 = map𝑇𝑚𝑠 _[ σ ]𝐸𝑙 𝓈s

[][]𝐸𝑙𝑠 : {Γ Δ Σ Ω : Ctx} (𝓈s : Elements Σ Ω) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  𝓈s [ σ ]𝐸𝑙𝑠 [ τ ]𝐸𝑙𝑠 ≡𝐸𝑙𝑠 𝓈s [ σ ∘𝑅𝑒𝑛 τ ]𝐸𝑙𝑠
[][]𝐸𝑙𝑠 ! σ τ = tt
[][]𝐸𝑙𝑠 (𝓈s ⊕ 𝓈) σ τ = [][]𝐸𝑙𝑠 𝓈s σ τ , [][]𝐸𝑙 𝓈 σ τ

infix 30 _[_]𝐸𝑙𝑠-S
_[_]𝐸𝑙𝑠-S : {Γ Δ Σ : Ctx} → SafeElements Δ Σ → Ren Γ Δ → SafeElements Γ Σ
𝓈s [ σ ]𝐸𝑙𝑠-S = map𝑇𝑚𝑠 _[ σ ]𝐸𝑙-S 𝓈s

qs : {Γ Δ : Ctx} → Elements Γ Δ → Nfs Γ Δ
qs = map𝑇𝑚𝑠 q

us : {Γ Δ : Ctx} → Nes Γ Δ → Elements Γ Δ
us = map𝑇𝑚𝑠 u

us-S : {Γ Δ : Ctx} → Nes Γ Δ → SafeElements Γ Δ
us-S = map𝑇𝑚𝑠 u-S

qs-nat : {Σ : Ctx} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈s : Elements Δ Σ) →
  qs (𝓈s [ σ ]𝐸𝑙𝑠) ≡ qs 𝓈s [ σ ]NFS
qs-nat σ ! = refl
qs-nat σ (𝓈s ⊕ 𝓈) =
  qs (𝓈s [ σ ]𝐸𝑙𝑠) ⊕ q (𝓈 [ σ ]𝐸𝑙)
    ≡⟨ ap (qs (𝓈s [ σ ]𝐸𝑙𝑠) ⊕_) (q-nat σ 𝓈) ⟩
  qs (𝓈s [ σ ]𝐸𝑙𝑠) ⊕ q 𝓈 [ σ ]NF
    ≡⟨ ap (_⊕ q 𝓈 [ σ ]NF) (qs-nat σ 𝓈s) ⟩
  (qs (𝓈s ⊕ 𝓈) [ σ ]NFS)
    ∎

comps : {Γ Δ : Ctx} (NS : Nes Γ Δ) →
  ParallelSteps (ιNfs (qs (us NS))) (ιNes NS)
comps ! = ∅𝑆
comps (NS ⊕ N) = comps NS ⊕𝑆 comp N

eval-⦇α⦈ : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Elements Γ Δ → Element Γ A
eval-⦇α⦈-ext : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) {𝓈s 𝓉s : Elements Γ Δ} →
  𝓈s ≡𝐸𝑙𝑠 𝓉s → eval-⦇α⦈ t 𝓈s ≡𝐸𝑙 eval-⦇α⦈ t 𝓉s
eval-⦇α⦈-hom : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Ren Γ Δ) (𝓈s : Elements Δ Σ) →
  eval-⦇α⦈ t 𝓈s [ σ ]𝐸𝑙 ≡𝐸𝑙 eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠)

eval-⦇α⦈ (V v) 𝓈s = derive 𝓈s v
eval-⦇α⦈ (Lam t) 𝓈s =
  El
    (λ σ 𝓈 → eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠 ⊕ 𝓈))
    (λ σ a → eval-⦇α⦈-ext t (refl𝐸𝑙𝑠 , a))
    (λ σ 𝓈 τ →
      eval-⦇α⦈-hom t τ (𝓈s [ σ ]𝐸𝑙𝑠 ⊕ 𝓈)
      ∙𝐸𝑙 eval-⦇α⦈-ext t ([][]𝐸𝑙𝑠 𝓈s σ τ , refl𝐸𝑙))
eval-⦇α⦈ {Γ} (App t s) 𝓈s =
  ob (eval-⦇α⦈ t 𝓈s) (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s 𝓈s)

ap-derive : {Γ Δ : Ctx} {A : Ty} (v : Var Δ A) {𝓈s 𝓉s : Elements Γ Δ} →
  𝓈s ≡𝐸𝑙𝑠 𝓉s → derive 𝓈s v ≡𝐸𝑙 derive 𝓉s v
ap-derive 𝑧𝑣 {𝓉s ⊕ 𝓉} {𝓈s ⊕ 𝓈} (as , a) = a
ap-derive (𝑠𝑣 v) {𝓉s ⊕ 𝓉} {𝓈s ⊕ 𝓈} (as , a) = ap-derive v as

≡𝐸𝑙[] : {Γ Δ : Ctx} {A : Ty} {𝓈 𝓉 : Element Δ A} → 𝓈 ≡𝐸𝑙 𝓉 → (σ : Ren Γ Δ) →
  𝓈 [ σ ]𝐸𝑙 ≡𝐸𝑙 𝓉 [ σ ]𝐸𝑙
≡𝐸𝑙[] {A = Base c} a σ = ap (_[ σ ]NF) a
≡𝐸𝑙[] {A = A ⇒ B} a σ τ 𝓈 = a (σ ∘𝑅𝑒𝑛 τ) 𝓈

≡𝐸𝑙𝑠[] : {Γ Δ Σ : Ctx} {𝓈s 𝓉s : Elements Δ Σ} → 𝓈s ≡𝐸𝑙𝑠 𝓉s → (σ : Ren Γ Δ) →
  𝓈s [ σ ]𝐸𝑙𝑠 ≡𝐸𝑙𝑠 𝓉s [ σ ]𝐸𝑙𝑠
≡𝐸𝑙𝑠[] {𝓈s = !} { ! } tt σ = tt
≡𝐸𝑙𝑠[] {𝓈s = 𝓈s ⊕ 𝓈} {𝓉s ⊕ 𝓉} (as , a) σ = ≡𝐸𝑙𝑠[] as σ , ≡𝐸𝑙[] a σ

eval-⦇α⦈-ext (V v) as = ap-derive v as
eval-⦇α⦈-ext (Lam t) as σ 𝓈 = eval-⦇α⦈-ext t (≡𝐸𝑙𝑠[] as σ , refl𝐸𝑙)
eval-⦇α⦈-ext {Γ} (App t s) {𝓈s} {𝓉s} as =
  eval-⦇α⦈-ext t as (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s 𝓈s)
  ∙𝐸𝑙 ext (eval-⦇α⦈ t 𝓉s) (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈-ext s as)

derive[]𝐸𝑙 : {Γ Δ Σ : Ctx} {A : Ty} (v : Var Σ A) (𝓈s : Elements Δ Σ) (τ : Ren Γ Δ) →
  derive 𝓈s v [ τ ]𝐸𝑙 ≡ derive (𝓈s [ τ ]𝐸𝑙𝑠) v
derive[]𝐸𝑙 𝑧𝑣 (𝓈s ⊕ 𝓈) τ = refl
derive[]𝐸𝑙 (𝑠𝑣 v) (𝓈s ⊕ 𝓈) τ = derive[]𝐸𝑙 v 𝓈s τ 

eval-⦇α⦈-hom (V v) σ 𝓈s = ⟪ derive[]𝐸𝑙 v 𝓈s σ ⟫
eval-⦇α⦈-hom (Lam t) σ 𝓈s τ 𝓉 =  eval-⦇α⦈-ext t ([][]𝐸𝑙𝑠 𝓈s σ τ ⁻¹𝐸𝑙𝑠 , refl𝐸𝑙)
eval-⦇α⦈-hom {Γ} {Δ} {Σ} (App t s) σ 𝓈s =
  hom (eval-⦇α⦈ t 𝓈s) (id𝑅𝑒𝑛 Δ) (eval-⦇α⦈ s 𝓈s) σ
  ∙𝐸𝑙 ⟪ ap (λ x → ob (eval-⦇α⦈ t 𝓈s) x (eval-⦇α⦈ s 𝓈s [ σ ]𝐸𝑙)) (∘𝑅𝑒𝑛IdL σ) ⟫
  ∙𝐸𝑙 ⟪ ap (λ x → ob (eval-⦇α⦈ t 𝓈s) x (eval-⦇α⦈ s 𝓈s [ σ ]𝐸𝑙)) (∘𝑅𝑒𝑛IdR σ ⁻¹) ⟫
  ∙𝐸𝑙 ext (eval-⦇α⦈ t 𝓈s) (σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Γ) (eval-⦇α⦈-hom s σ 𝓈s)
  ∙𝐸𝑙 eval-⦇α⦈-hom t σ 𝓈s (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s (𝓈s [ σ ]𝐸𝑙𝑠))

forget : {Γ Δ : Ctx} → SafeElements Γ Δ → Elements Γ Δ
forget = map𝑇𝑚𝑠 fst

forget[]𝐸𝑙𝑠 : {Γ Δ Σ : Ctx} (𝓈s : SafeElements Δ Σ) (σ :  Ren Γ Δ) →
  forget (𝓈s [ σ ]𝐸𝑙𝑠-S) ≡ forget 𝓈s [ σ ]𝐸𝑙𝑠
forget[]𝐸𝑙𝑠 𝓈s σ = (map𝑇𝑚𝑠comp fst _[ σ ]𝐸𝑙-S 𝓈s) ∙ (map𝑇𝑚𝑠comp _[ σ ]𝐸𝑙 fst 𝓈s ⁻¹)

eval-nat : {Γ : Ctx} {A : Ty} (t : Tm Γ A) {Δ : Ctx} (𝓈s : SafeElements Δ Γ) →
  Steps (ιNf (q (eval-⦇α⦈ t (forget 𝓈s)))) (t [ ιNfs (qs (forget 𝓈s)) ])

eval-⦇α⦈-safe : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (𝓈s : SafeElements Γ Δ) →
  SafeType (eval-⦇α⦈ t (forget 𝓈s))

eval-⦇α⦈-safe (V v) 𝓈s = my-derive 𝓈s v where
  my-derive : {Γ Δ : Ctx} {A : Ty} (𝓈s : SafeElements Γ Δ) (v : Var Δ A) →
    SafeType (derive (forget 𝓈s) v)
  my-derive (𝓈s ⊕ 𝓈) 𝑧𝑣 = snd 𝓈
  my-derive (𝓈s ⊕ 𝓈) (𝑠𝑣 v) = my-derive 𝓈s v
eval-⦇α⦈-safe (Lam t) 𝓈s σ 𝓉 =
  [] ∷≡ ap (λ x → (ιNf (q (eval-⦇α⦈ t (x ⊕ fst 𝓉))))) (forget[]𝐸𝑙𝑠 𝓈s σ ⁻¹)
    ⊙ eval-nat t (𝓈s [ σ ]𝐸𝑙𝑠-S ⊕ 𝓉)
    ∷≡
      (t [ ιNfs (qs (forget (𝓈s [ σ ]𝐸𝑙𝑠-S))) ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ ap (λ x → t [ ιNfs (qs x) ⊕ ιNf (q (fst 𝓉)) ]) (forget[]𝐸𝑙𝑠 𝓈s σ) ⟩
      t [ ιNfs (qs (forget 𝓈s [ σ ]𝐸𝑙𝑠)) ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ ap (λ x → t [ ιNfs x ⊕ ιNf (q (fst 𝓉)) ]) (qs-nat σ (forget 𝓈s)) ⟩
      t [ ιNfs (qs (forget 𝓈s) [ σ ]NFS) ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ ap (λ x → t [ x ⊕ ιNf (q (fst 𝓉)) ]) (ιNfsLem (qs (forget 𝓈s)) σ) ⟩
      t [ ιNfs (qs (forget 𝓈s)) ∘Tms varify σ ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ lem t (ιNfs (qs (forget 𝓈s)) ∘Tms varify σ) (ιNf (q (fst 𝓉))) ⁻¹ ⟩
      t [ W₂Tms _ (ιNfs (qs (forget 𝓈s)) ∘Tms varify σ) ] [ idTms _ ⊕ ιNf (q (fst 𝓉)) ]
        ∎)
    ∷ ⟨ 𝑂 ⊚ β (t [ W₂Tms _ (ιNfs (qs (forget 𝓈s)) ∘Tms varify σ) ]) (ιNf (q (fst 𝓉))) ⟩⁻¹
    ∷≡ ap (λ x → App x (ιNf (q (fst 𝓉)))) ([][] (Lam t) (ιNfs (qs (forget 𝓈s))) (varify σ) ⁻¹)
    ⊙ deepens (𝐴₁ 𝑂 (ιNf (q (fst 𝓉)))) ((invertSteps (eval-nat (Lam t) 𝓈s)) [ varify σ ]𝑆')
    ∷≡
      (App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
        [ W₂Tms _ (varify σ) ])) (ιNf (q (fst 𝓉)))
        ≡⟨ ap (λ x → App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠)
          ⊕ u (VN 𝑧𝑣)))) [ x ⊕ 𝑧 ])) (ιNf (q (fst 𝓉)))) (Vlem2 σ ⁻¹) ⟩
      App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
        [ varify (W₂𝑅𝑒𝑛 _ σ) ])) (ιNf (q (fst 𝓉)))
        ≡⟨ ap (λ x → App (Lam x) (ιNf (q (fst 𝓉))))
          (ιNfLem (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠)
          ⊕ u (VN 𝑧𝑣)))) (W₂𝑅𝑒𝑛 _ σ) ⁻¹) ⟩
      App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣)))
        [ W₂𝑅𝑒𝑛 _ σ ]NF))) (ιNf (q (fst 𝓉)))
        ∎) ,
    (tr (λ x → SafeType (eval-⦇α⦈ t (x ⊕ fst 𝓉)))
      (forget[]𝐸𝑙𝑠 𝓈s σ)
      (eval-⦇α⦈-safe t (𝓈s [ σ ]𝐸𝑙𝑠-S ⊕ 𝓉)))  where
  lem : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (σ : Tms Γ Δ) (s : Tm Γ A) →
          t [ W₂Tms A σ ] [ idTms Γ ⊕ s ] ≡ t [ σ ⊕ s ]
  lem {Γ} {Δ} {A} t σ s =
    t [ W₂Tms A σ ] [ idTms Γ ⊕ s ]
      ≡⟨ [][] t (W₂Tms A σ) (idTms Γ ⊕ s) ⟩
    t [ W₁Tms A σ ∘Tms (idTms Γ ⊕ s) ⊕ s ]
      ≡⟨ ap (λ x → t [ x  ⊕ s ]) (Wlem1 σ (idTms Γ) s) ⟩
    t [ σ ∘Tms idTms Γ ⊕ s ]
      ≡⟨ ap (λ x → t [ x ⊕ s ]) (∘TmsIdR σ) ⟩
    t [ σ ⊕ s ]
      ∎
eval-⦇α⦈-safe {Γ} (App t s) 𝓈s =
  snd (eval-⦇α⦈-safe t 𝓈s (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s (forget 𝓈s) , eval-⦇α⦈-safe s 𝓈s))

eval-nat (V v) 𝓈s =
  [] ∷≡ ((deriveMap ιNf (qs (forget 𝓈s)) v ∙ ap ιNf (deriveMap q (forget 𝓈s) v)) ⁻¹) 
eval-nat {Γ} {A ⇒ B} (Lam t) {Δ} 𝓈s =
  []
    ∷≡
      ap (λ x → Lam (ιNf (q (eval-⦇α⦈ t (x ⊕ u (VN 𝑧𝑣)))))) (forget[]𝐸𝑙𝑠 𝓈s (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) ⁻¹)
    ⊙ deepens (𝐿 𝑂) (eval-nat t (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠-S ⊕ (u (VN 𝑧𝑣) , u-safe (VN 𝑧𝑣))))
    ∷≡
      ap (λ x → Lam (t [ ιNfs (qs x) ⊕ ιNf (q (u (VN 𝑧𝑣))) ])) (forget[]𝐸𝑙𝑠 𝓈s (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)))
    ⊙ deepens (𝐿 𝑂) (t [ idParallel (ιNfs (qs (forget 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠)))
      ⊕𝑆 comp (VN 𝑧𝑣) ]𝑆)
    ∷≡
      (Lam (t [ ιNfs (qs (forget 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠)) ⊕ 𝑧 ])
        ≡⟨ ap (λ x → Lam (t [ ιNfs x ⊕ 𝑧 ])) (qs-nat (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (forget 𝓈s)) ⟩
      Lam (t [ ιNfs (qs (forget 𝓈s) [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]NFS) ⊕ 𝑧 ])
        ≡⟨ ap (λ x → Lam (t [ x ⊕ 𝑧 ])) (ιNfsLem (qs (forget 𝓈s)) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ))) ⟩
      Lam (t [ ιNfs (qs (forget 𝓈s)) ∘Tms π ⊕ 𝑧 ])
        ≡⟨ ap (λ x → Lam (t [ x ⊕ 𝑧 ])) (Wlem6 (ιNfs (qs (forget 𝓈s)))) ⟩
      Lam (t [ W₂Tms A (ιNfs (qs (forget 𝓈s))) ])
        ∎)
eval-nat (App t s) 𝓈s =
  fst (eval-⦇α⦈-safe t 𝓈s (id𝑅𝑒𝑛 _) (eval-⦇α⦈ s (forget 𝓈s) , eval-⦇α⦈-safe s 𝓈s))
    ∷≡ ap (λ x → (App (ιNf x) (ιNf (q (eval-⦇α⦈ s (forget 𝓈s))))))
      ([id]NF (q (eval-⦇α⦈ t (forget 𝓈s))))
    ⊙ deepens (𝐴₁ 𝑂 (ιNf (q (eval-⦇α⦈ s (forget 𝓈s))))) (eval-nat t 𝓈s)
    ⊙ deepens (𝐴₂ (t [ ιNfs (qs (forget 𝓈s)) ]) 𝑂) (eval-nat s 𝓈s)

idNes : (Γ : Ctx) → Nes Γ Γ
idNes Γ = map𝑇𝑚𝑠 VN (id𝑅𝑒𝑛 Γ)

ιidNes : (Γ : Ctx) → ιNes (idNes Γ) ≡ idTms Γ
ιidNes ∅ = refl
ιidNes (Γ ⊹ A) = ap (_⊕ 𝑧) (map𝑇𝑚𝑠comp ιNe VN (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)))

norm : {Γ : Ctx} {A : Ty} → Tm Γ A → Nf Γ A
norm {Γ} t = q (eval-⦇α⦈ t (us (idNes Γ)))

forget-us-S : {Γ Δ : Ctx} (NS : Nes Γ Δ) →
  forget (us-S NS) ≡ us NS
forget-us-S ! = refl
forget-us-S (NS ⊕ N) = ap (_⊕ u N) (forget-us-S NS)

trace : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
  Steps t (ιNf (norm t))
trace {Γ} t =
  []
    ∷≡
      (t
        ≡⟨ [id] t ⁻¹ ⟩
      t [ idTms Γ ]
        ≡⟨ ap (t [_]) (ιidNes Γ ⁻¹) ⟩
      t [ ιNes (idNes Γ) ]
        ∎)
    ⊙ invertSteps (t [ comps (idNes Γ) ]𝑆)
    ∷≡ ap (λ x → t [ ιNfs (qs x) ]) (forget-us-S (idNes Γ) ⁻¹)
    ⊙ invertSteps (eval-nat t (us-S (idNes Γ)))
    ∷≡ ap (λ x → ιNf (q (eval-⦇α⦈ t x))) (forget-us-S (idNes Γ))
