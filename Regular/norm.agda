module norm where

open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public

open import lists
open import syn
open import normal
open import trace

data ⊤ : Type lzero where
  tt : ⊤

Element : Ctx → Ty → Type lzero
Element Γ (Base X) = Nf Γ (Base X)
Element Γ (A ⇒ B) = {Δ : Ctx} → Ren Δ Γ → Element Δ A → Element Δ B

infix 30 _[_]𝐸𝑙
_[_]𝐸𝑙 : {Γ Δ : Ctx} {A : Ty} → Element Δ A → Ren Γ Δ → Element Γ A
_[_]𝐸𝑙 {A = Base x} 𝓈 σ = 𝓈 [ σ ]NF
_[_]𝐸𝑙 {A = A ⇒ B} 𝒻 σ τ 𝓈 = 𝒻 (σ ∘𝑅𝑒𝑛 τ) 𝓈

q : {Γ : Ctx} {A : Ty} → Element Γ A → Nf Γ A
u : {Γ : Ctx} {A : Ty} → Ne Γ A → Element Γ A

q {A = Base X} 𝓈 = 𝓈
q {Γ} {A ⇒ B} 𝒻 = LAM (q (𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))

u {A = Base X} M = NEU M
u {A = A ⇒ B} M σ 𝓈 = u (APP (M [ σ ]NE) (q 𝓈))

cmp : {Γ : Ctx} {A : Ty} (N : Ne Γ A) → Steps (ιNf (q (u N))) (ιNe N)
cmp {A = Base s} N = []
cmp {Γ} {A ⇒ B} N =
  tr (λ t → Steps (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))))) t)
    (Lam (App (ιNe (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE)) (V 𝑧𝑣))
      ≡⟨ ap (λ x → Lam (App x (V 𝑧𝑣))) (ιNeLem N (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ))) ⟩
    Lam (App (ιNe N [ π ]) (V 𝑧𝑣))
      ≡⟨ ap (λ x → Lam (App x (V 𝑧𝑣))) (Wlem5 (ιNe N)) ⟩
    Lam (App (W₁Tm A (ιNe N)) (V 𝑧𝑣))
      ∎)
    (deepens (𝐿 𝑂) (cmp (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
      ⊙ deepens (𝐿 (𝐴₂ (ιNe (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE)) 𝑂)) (cmp (VN 𝑧𝑣)))
  ∷ ⟨ 𝑂 ⊚ η (ιNe N) ⟩⁻¹

{-NaturalType : {Γ : Ctx} {A : Ty} (𝓈 : Element Γ A) → Type lzero

NaturalElement : Ctx → Ty → Type lzero
NaturalElement Γ A = Σ (Element Γ A) NaturalType

NaturalType {Γ} {Base c} 𝓈 = ⊤
NaturalType {Γ} {A ⇒ B} 𝒻 =
  {Δ : Ctx} (σ : Ren Δ Γ) (𝓈 : NaturalElement Δ A) →
    ({Σ : Ctx} (τ : Ren Σ Δ) → 𝒻 σ (fst 𝓈) [ τ ]𝐸𝑙 ≡ 𝒻 (σ ∘𝑅𝑒𝑛 τ) (fst 𝓈 [ τ ]𝐸𝑙))
    × NaturalType (𝒻 σ (fst 𝓈))-}

_≡𝐸𝑙_ : {Γ : Ctx} {A : Ty} (𝓈 𝓉 : Element Γ A) → Type lzero
_≡𝐸𝑙_ {Γ} {Base c} N M = N ≡ M
_≡𝐸𝑙_ {Γ} {A ⇒ B} 𝒻 ℊ = {Δ : Ctx} (σ : Ren Δ Γ) (𝓈 : Element Δ A) → 𝒻 σ 𝓈 ≡ ℊ σ 𝓈

SafeType : {Γ : Ctx} {A : Ty} (𝓈 : Element Γ A) → Type lzero

SafeElement : Ctx → Ty → Type lzero
SafeElement Γ A = Σ (Element Γ A) SafeType

{-# NO_POSITIVITY_CHECK #-}
record SafeType⇒ {Γ Δ : Ctx} {A B : Ty} (𝒻 : Element Γ (A ⇒ B)) (σ : Ren Δ Γ) (𝓈 : SafeElement Δ A)
       : Type lzero where
  inductive
  field
    ext : (𝓉 : SafeElement Δ A) → fst 𝓈 ≡𝐸𝑙 fst 𝓉 → 𝒻 σ (fst 𝓈) ≡ 𝒻 σ (fst 𝓉)
    hom : {Σ : Ctx} (τ : Ren Σ Δ) → 𝒻 σ (fst 𝓈) [ τ ]𝐸𝑙 ≡𝐸𝑙 𝒻 (σ ∘𝑅𝑒𝑛 τ) (fst 𝓈 [ τ ]𝐸𝑙)
    nat : Steps (ιNf (q (𝒻 σ (fst 𝓈)))) (App (ιNf (q 𝒻 [ σ ]NF)) (ιNf (q (fst 𝓈))))
    preserve : SafeType (𝒻 σ (fst 𝓈))

SafeType {Γ} {Base c} 𝓈 = ⊤
SafeType {Γ} {A ⇒ B} 𝒻 =
  {Δ : Ctx} (σ : Ren Δ Γ) (𝓈 : SafeElement Δ A) → SafeType⇒ 𝒻 σ 𝓈
    {-({Σ : Ctx} (τ : Ren Σ Δ) → 𝒻 σ (fst 𝓈) [ τ ]𝐸𝑙 ≡𝐸𝑙 𝒻 (σ ∘𝑅𝑒𝑛 τ) (fst 𝓈 [ τ ]𝐸𝑙))
    × Steps (ιNf (q (𝒻 σ (fst 𝓈))))
          (App (ιNf (q 𝒻 [ σ ]NF)) (ιNf (q (fst 𝓈))))
    × SafeType (𝒻 σ (fst 𝓈))-}

u-hom : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (N : Ne Δ A) →
  u (N [ σ ]NE) ≡𝐸𝑙 u N [ σ ]𝐸𝑙
u-hom {Base x} σ N = refl
u-hom {A ⇒ B} σ N τ 𝓈 = ap (λ x → u (APP x (q 𝓈))) ([][]NE N σ τ)

q-hom : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈 : SafeElement Δ A) →
  q (fst 𝓈 [ σ ]𝐸𝑙) ≡ q (fst 𝓈) [ σ ]NF
q-hom {Base x} σ 𝓈 = refl
q-hom {A ⇒ B} {Γ} {Δ} σ 𝒻 =
  {!(u-hom (W₂𝑅𝑒𝑛 A σ) (VN 𝑧𝑣))
  {-LAM (q (fst 𝒻 (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))
    ∎-}
  {-LAM (q (fst 𝒻 (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))
    ≡⟨ ap (λ x → LAM (q (fst 𝒻 x (u-hom (W₂𝑅𝑒𝑛 A σ) (VN 𝑧𝑣) i)))) lem ⟩
  LAM (q (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A σ) (u (VN 𝑧𝑣) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)))
    ≡⟨ {!(λ i → LAM (q (hom 𝒻 (W₂𝑅𝑒𝑛 A σ) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) (~ i))))!} ⟩
  LAM (q (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙))
    ≡⟨ ap LAM (q-hom (W₂𝑅𝑒𝑛 A σ)
      (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) , ?)) ⟩
  LAM (q (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣))) [ W₂𝑅𝑒𝑛 A σ ]NF)
    ∎-}!}
     where
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

{-_[_]𝐸𝑙-nat : {Γ Δ : Ctx} {A : Ty} (𝓈 : NaturalElement Δ A) (σ : Ren Γ Δ) →
  NaturalType (fst 𝓈 [ σ ]𝐸𝑙)
_[_]𝐸𝑙-nat {A = Base c} 𝓈 σ = tt
_[_]𝐸𝑙-nat {A = A ⇒ B} 𝒻 σ τ 𝓈 =
  (λ μ →
    fst 𝒻 (σ ∘𝑅𝑒𝑛 τ) (fst 𝓈) [ μ ]𝐸𝑙
      ≡⟨ fst ((snd 𝒻) (σ ∘𝑅𝑒𝑛 τ) 𝓈) μ ⟩
    fst 𝒻 (σ ∘𝑅𝑒𝑛 τ ∘𝑅𝑒𝑛 μ) (fst 𝓈 [ μ ]𝐸𝑙)
      ≡⟨ ap (λ x → fst 𝒻 x (fst 𝓈 [ μ ]𝐸𝑙)) (∘𝑅𝑒𝑛Assoc σ τ μ) ⟩
    fst 𝒻 (σ ∘𝑅𝑒𝑛 (τ ∘𝑅𝑒𝑛 μ)) (fst 𝓈 [ μ ]𝐸𝑙)
      ∎) ,
    snd ((snd 𝒻) (σ ∘𝑅𝑒𝑛 τ) 𝓈)-}

{-q-hom : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈 : NaturalElement Δ A) →
  q (fst 𝓈 [ σ ]𝐸𝑙) ≡ q (fst 𝓈) [ σ ]NF
u-hom : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (N : Ne Δ A) →
  u (N [ σ ]NE) ≡ u N [ σ ]𝐸𝑙

q-hom {Base x} σ 𝓈 = refl
q-hom {A ⇒ B} {Γ} {Δ} σ 𝒻 =
  LAM (q (fst 𝒻 (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))
    ≡⟨ ap (λ x → LAM (q (fst 𝒻 x (u-hom (W₂𝑅𝑒𝑛 A σ) (VN 𝑧𝑣) i)))) lem ⟩
  LAM (q (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A σ) (u (VN 𝑧𝑣) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)))
    ≡⟨ {!(λ i → LAM (q (hom 𝒻 (W₂𝑅𝑒𝑛 A σ) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) (~ i))))!} ⟩
  LAM (q (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙))
    ≡⟨ ap LAM (q-hom (W₂𝑅𝑒𝑛 A σ)
      (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) , ?)) ⟩
  LAM (q (fst 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣))) [ W₂𝑅𝑒𝑛 A σ ]NF)
    ∎
     where
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

u-hom {Base x} σ N = refl
u-hom {A ⇒ B} σ N = {!ap (λ x → u (APP x (q 𝓈))) ([][]NE N σ τ)!}

SafeType : {Γ : Ctx} {A : Ty} (𝓈 : NaturalElement Γ A) → Type lzero

SafeElement : Ctx → Ty → Set
SafeElement Γ A = Σ (NaturalElement Γ A) SafeType

SafeType {Γ} {Base c} N = ⊤
SafeType {Γ} {A ⇒ B} 𝒻 =
  {Δ : Ctx} (σ : Ren Δ Γ) (𝓈 : SafeElement Δ A) →
    Steps (ιNf (q (fst 𝒻 σ (fst (fst 𝓈)))))
          (App (ιNf (q (fst 𝒻) [ σ ]NF)) (ιNf (q (fst (fst 𝓈)))))
      ×  {!SafeType (fst 𝒻 σ (fst (fst 𝓈)))!}-}

{-infix 30 _[_]𝐸𝑙
_[_]𝐸𝑙 : {Γ Δ : Ctx} {A : Ty} → Element Δ A → Ren Γ Δ → Element Γ A
_[_]𝐸𝑙 {A = Base x} 𝓈 σ = 𝓈 [ σ ]NF
_[_]𝐸𝑙 {A = A ⇒ B} 𝒻 σ =
  nat
    (λ τ 𝓈 → (ob 𝒻) (σ ∘𝑅𝑒𝑛 τ) 𝓈)
    (λ τ μ 𝓈 →
      ob 𝒻 (σ ∘𝑅𝑒𝑛 μ) 𝓈 [ τ ]𝐸𝑙
        ≡⟨ hom 𝒻 τ (σ ∘𝑅𝑒𝑛 μ) 𝓈 ⟩
      ob 𝒻 (σ ∘𝑅𝑒𝑛 μ ∘𝑅𝑒𝑛 τ) (𝓈 [ τ ]𝐸𝑙)
        ≡⟨ ap (λ x → ob 𝒻 x (𝓈 [ τ ]𝐸𝑙)) (∘𝑅𝑒𝑛Assoc σ μ τ) ⟩
      ob 𝒻 (σ ∘𝑅𝑒𝑛 (μ ∘𝑅𝑒𝑛 τ)) (𝓈 [ τ ]𝐸𝑙)
        ∎)

q : {Γ : Ctx} {A : Ty} → Element Γ A → Nf Γ A
u : {Γ : Ctx} {A : Ty} → Ne Γ A → Element Γ A

q {A = Base X} 𝓈 = 𝓈
q {Γ} {A ⇒ B} 𝒻 = LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))-}



{-postulate
  ≡Element⇒ : {Γ : Ctx} {A B : Ty} {𝒻 ℊ : Element⇒ Γ A B} →
    Path ({Δ : Ctx} → Ren Δ Γ → Element Δ A → Element Δ B) (ob 𝒻) (ob ℊ) → 𝒻 ≡ ℊ

[id]𝐸𝑙 : {Γ : Ctx} {A : Ty} (𝓈 : Element Γ A) → 𝓈 [ id𝑅𝑒𝑛 Γ ]𝐸𝑙 ≡ 𝓈
[id]𝐸𝑙 {Γ} {Base c} N = [id]NF N
[id]𝐸𝑙 {Γ} {A ⇒ B} (nat 𝒻 p) = ≡Element⇒ (λ i τ → 𝒻 (∘𝑅𝑒𝑛IdL τ i))

[][]𝐸𝑙 : {Γ Δ Σ : Ctx} {A : Ty} (𝓈 : Element Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  𝓈 [ σ ]𝐸𝑙 [ τ ]𝐸𝑙 ≡ 𝓈 [ σ ∘𝑅𝑒𝑛 τ ]𝐸𝑙
[][]𝐸𝑙 {A = Base c} N σ τ = [][]NF N σ τ
[][]𝐸𝑙 {A = A ⇒ B} 𝒻 σ τ = ≡Element⇒ (λ i μ → ob 𝒻 (∘𝑅𝑒𝑛Assoc σ τ μ (~ i)))

q : {Γ : Ctx} {A : Ty} → Element Γ A → Nf Γ A
u : {Γ : Ctx} {A : Ty} → Ne Γ A → Element Γ A

q {A = Base X} 𝓈 = 𝓈
q {Γ} {A ⇒ B} 𝒻 = LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))

q-nat : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈 : Element Δ A) →
  q (𝓈 [ σ ]𝐸𝑙) ≡ q 𝓈 [ σ ]NF
u-nat : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (N : Ne Δ A) →
  u (N [ σ ]NE) ≡ u N [ σ ]𝐸𝑙

u {A = Base X} M = NEU M
u {A = A ⇒ B} M =
  nat
    (λ σ 𝓈 → u (APP (M [ σ ]NE) (q 𝓈)))
    (λ σ τ 𝓈 →
      u (APP (M [ τ ]NE) (q 𝓈)) [ σ ]𝐸𝑙
        ≡⟨ u-nat σ (APP (M [ τ ]NE) (q 𝓈)) ⁻¹ ⟩
      u (APP (M [ τ ]NE [ σ ]NE) (q 𝓈 [ σ ]NF))
        ≡⟨ (λ i → u (APP ([][]NE M τ σ i) (q-nat σ 𝓈 (~ i)))) ⟩
      u (APP (M [ τ ∘𝑅𝑒𝑛 σ ]NE) (q (𝓈 [ σ ]𝐸𝑙)))
        ∎)

cmp : {Γ : Ctx} {A : Ty} (N : Ne Γ A) → Steps (ιNf (q (u N))) (ιNe N)
cmp {A = Base s} N = []
cmp {Γ} {A ⇒ B} N =
  deepens (𝐿 𝑂) (cmp (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
    ⊙ deepens (𝐿 (𝐴₂ (ιNe (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE)) 𝑂)) (cmp (VN 𝑧𝑣))
    ∷ sub⟨ (λ i → Lam (App (ιNeLem N (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) i) (V 𝑧𝑣))) ⟩
    ∷ ⟨ 𝑂 ⊚ η (ιNe N) ⟩⁻¹

q-nat {Base x} σ 𝓈 = refl
q-nat {A ⇒ B} {Γ} {Δ} σ 𝒻 =
  LAM (q (ob 𝒻 (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))
    ≡⟨ (λ i → LAM (q (ob 𝒻 (lem i) (u-nat (W₂𝑅𝑒𝑛 A σ) (VN 𝑧𝑣) i)))) ⟩
  LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A σ) (u (VN 𝑧𝑣) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)))
    ≡⟨ (λ i → LAM (q (hom 𝒻 (W₂𝑅𝑒𝑛 A σ) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) (~ i)))) ⟩
  LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)) [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙))
    ≡⟨ ap LAM (q-nat (W₂𝑅𝑒𝑛 A σ) (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣)))) ⟩
  LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (u (VN 𝑧𝑣))) [ W₂𝑅𝑒𝑛 A σ ]NF)
    ∎
     where
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

u-nat {Base x} σ N = refl
u-nat {A ⇒ B} σ N =
  ≡Element⇒ (λ i τ 𝓈 → u (APP ([][]NE N σ τ i) (q 𝓈)))

SafeType : {Γ : Ctx} {A : Ty} (𝓈 : Element Γ A) → Type

SafeElement : Ctx → Ty → Set
SafeElement Γ A = Σ (Element Γ A) SafeType

postulate
  ≡SafeElement : {Γ : Ctx} {A : Ty} {𝒻 ℊ : SafeElement Γ A} →
    fst 𝒻 ≡ fst ℊ → 𝒻 ≡ ℊ

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
    ∷ sub⟨
      App (ιNf (q (fst 𝓈) [ σ ∘𝑅𝑒𝑛 τ ]NF)) (ιNf (q (fst 𝓉)))
        ≡⟨ (λ i → App (ιNf ([][]NF (q (fst 𝓈)) σ τ (~ i))) (ιNf (q (fst 𝓉)))) ⟩
      App (ιNf (q (fst 𝓈) [ σ ]NF [ τ ]NF)) (ιNf (q (fst 𝓉)))
        ≡⟨ (λ i → App (ιNf (q-nat σ (fst 𝓈) (~ i) [ τ ]NF)) (ιNf (q (fst 𝓉)))) ⟩
      App (ιNf (q (fst 𝓈 [ σ ]𝐸𝑙) [ τ ]NF)) (ιNf (q (fst 𝓉)))
        ∎  ⟩ ,
    snd (snd 𝓈 (σ ∘𝑅𝑒𝑛 τ) 𝓉)

_[_]𝐸𝑙-S : {Γ Δ : Ctx} {A : Ty} → SafeElement Δ A → Ren Γ Δ → SafeElement Γ A
𝓈 [ σ ]𝐸𝑙-S = fst 𝓈 [ σ ]𝐸𝑙 , 𝓈 [ σ ]𝐸𝑙-safe

u-safe : {Γ : Ctx} {A : Ty} (N : Ne Γ A) → SafeType (u N)
u-safe {Γ} {Base c} N = tt
u-safe {Γ} {A ⇒ B} N σ 𝓈 =
  cmp (APP (N [ σ ]NE) (q (fst 𝓈)))
    ∷ sub⟨ (λ i → (App (ιNeLem N σ i) (ιNf (q (fst 𝓈))))) ⟩
    ⊙ deepens (𝐴₁ 𝑂 (ιNf (q (fst 𝓈)))) (invertSteps (cmp N) [ varify σ ]𝑆')
    ∷ sub⟨
      App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
        [ W₂Tms A (varify σ) ])) (ιNf (q (fst 𝓈)))
        ≡⟨ (λ i → App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
          [ Vlem2 σ (~ i) ⊕ 𝑧 ])) (ιNf (q (fst 𝓈)))) ⟩
      App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
        [ varify (W₂𝑅𝑒𝑛 A σ) ])) (ιNf (q (fst 𝓈)))
        ≡⟨ (λ i → App (Lam (ιNfLem (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
          (W₂𝑅𝑒𝑛 A σ) (~ i))) (ιNf (q (fst 𝓈)))) ⟩
      App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
        [ W₂𝑅𝑒𝑛 A σ ]NF))) (ιNf (q (fst 𝓈)))
        ∎ ⟩ ,
    u-safe (APP (N [ σ ]NE) (q (fst 𝓈)))

u-S : {Γ : Ctx} {A : Ty} → Ne Γ A → SafeElement Γ A
u-S N = u N , u-safe N

Elements = 𝑇𝑚𝑠 Element
SafeElements = 𝑇𝑚𝑠 SafeElement

qs : {Γ Δ : Ctx} → Elements Γ Δ → Nfs Γ Δ
qs = map𝑇𝑚𝑠 q

us : {Γ Δ : Ctx} → Nes Γ Δ → Elements Γ Δ
us = map𝑇𝑚𝑠 u

us-S : {Γ Δ : Ctx} → Nes Γ Δ → SafeElements Γ Δ
us-S = map𝑇𝑚𝑠 u-S

cmps : {Γ Δ : Ctx} (NS : Nes Γ Δ) →
  ParallelSteps (ιNfs (qs (us NS))) (ιNes NS)
cmps ! = ∅𝑆
cmps (NS ⊕ N) = cmps NS ⊕𝑆 cmp N

infix 30 _[_]𝐸𝑙𝑠
_[_]𝐸𝑙𝑠 : {Γ Δ Σ : Ctx} → Elements Δ Σ → Ren Γ Δ → Elements Γ Σ
𝓈s [ σ ]𝐸𝑙𝑠 = map𝑇𝑚𝑠 _[ σ ]𝐸𝑙 𝓈s

[][]𝐸𝑙𝑠 : {Γ Δ Σ Ω : Ctx} (𝓈s : Elements Σ Ω) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  𝓈s [ σ ]𝐸𝑙𝑠 [ τ ]𝐸𝑙𝑠 ≡ 𝓈s [ σ ∘𝑅𝑒𝑛 τ ]𝐸𝑙𝑠
[][]𝐸𝑙𝑠 ! σ τ = refl
[][]𝐸𝑙𝑠 (𝓈s ⊕ 𝓈) σ τ i = [][]𝐸𝑙𝑠 𝓈s σ τ i ⊕ [][]𝐸𝑙 𝓈 σ τ i

infix 30 _[_]𝐸𝑙𝑠-S
_[_]𝐸𝑙𝑠-S : {Γ Δ Σ : Ctx} → SafeElements Δ Σ → Ren Γ Δ → SafeElements Γ Σ
𝓈s [ σ ]𝐸𝑙𝑠-S = map𝑇𝑚𝑠 _[ σ ]𝐸𝑙-S 𝓈s

qs-nat : {Σ : Ctx} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈s : Elements Δ Σ) →
  qs (𝓈s [ σ ]𝐸𝑙𝑠) ≡ qs 𝓈s [ σ ]NFS
qs-nat σ ! = refl
qs-nat σ (𝓈s ⊕ 𝓈) i = qs-nat σ 𝓈s i ⊕ q-nat σ 𝓈 i

{-# TERMINATING #-}
eval-⦇α⦈ : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Elements Γ Δ → Element Γ A
eval-⦇α⦈-hom : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Ren Γ Δ) (𝓈s : Elements Δ Σ) →
  eval-⦇α⦈ t 𝓈s [ σ ]𝐸𝑙 ≡ eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠)

eval-⦇α⦈ (V v) 𝓈s = derive 𝓈s v
eval-⦇α⦈ (Lam t) 𝓈s =
  nat
    (λ σ 𝓉 → eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠 ⊕ 𝓉))
    (λ σ τ 𝓈 →
      eval-⦇α⦈ t ((𝓈s [ τ ]𝐸𝑙𝑠) ⊕ 𝓈) [ σ ]𝐸𝑙
        ≡⟨ eval-⦇α⦈-hom t σ (𝓈s [ τ ]𝐸𝑙𝑠 ⊕ 𝓈) ⟩
      eval-⦇α⦈ t (𝓈s [ τ ]𝐸𝑙𝑠 [ σ ]𝐸𝑙𝑠 ⊕ 𝓈 [ σ ]𝐸𝑙)
        ≡⟨ (λ i → eval-⦇α⦈ t ([][]𝐸𝑙𝑠 𝓈s τ σ i ⊕ 𝓈 [ σ ]𝐸𝑙)) ⟩
      eval-⦇α⦈ t (𝓈s [ τ ∘𝑅𝑒𝑛 σ ]𝐸𝑙𝑠 ⊕ 𝓈 [ σ ]𝐸𝑙)
        ∎)
eval-⦇α⦈ {Γ} (App t s) 𝓈s =
  ob (eval-⦇α⦈ t 𝓈s) (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s 𝓈s)

derive[]𝐸𝑙 : {Γ Δ Σ : Ctx} {A : Ty} (v : Var Σ A) (𝓈s : Elements Δ Σ) (τ : Ren Γ Δ) →
  derive 𝓈s v [ τ ]𝐸𝑙 ≡ derive (𝓈s [ τ ]𝐸𝑙𝑠) v
derive[]𝐸𝑙 𝑧𝑣 (𝓈s ⊕ 𝓈) τ = refl
derive[]𝐸𝑙 (𝑠𝑣 v) (𝓈s ⊕ 𝓈) τ = derive[]𝐸𝑙 v 𝓈s τ 

eval-⦇α⦈-hom (V v) σ 𝓈s = derive[]𝐸𝑙 v 𝓈s σ
eval-⦇α⦈-hom (Lam t) σ 𝓈s =
  ≡Element⇒ (λ i τ 𝓉 → eval-⦇α⦈ t ([][]𝐸𝑙𝑠 𝓈s σ τ (~ i) ⊕ 𝓉))
eval-⦇α⦈-hom {Γ} {Δ} {Σ} (App t s) σ 𝓈s =
  ob (eval-⦇α⦈ t 𝓈s) (id𝑅𝑒𝑛 Δ) (eval-⦇α⦈ s 𝓈s) [ σ ]𝐸𝑙
    ≡⟨ hom (eval-⦇α⦈ t 𝓈s) σ (id𝑅𝑒𝑛 Δ) (eval-⦇α⦈ s 𝓈s) ⟩
  ob (eval-⦇α⦈ t 𝓈s) (id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ) (eval-⦇α⦈ s 𝓈s [ σ ]𝐸𝑙)
    ≡⟨ (λ i → ob (eval-⦇α⦈ t 𝓈s) (∘𝑅𝑒𝑛IdR (∘𝑅𝑒𝑛IdL σ i) (~ i)) (eval-⦇α⦈-hom s σ 𝓈s i)) ⟩
  ob (eval-⦇α⦈ t 𝓈s) (σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s (𝓈s [ σ ]𝐸𝑙𝑠))
    ≡⟨ (λ i → ob (eval-⦇α⦈-hom t σ 𝓈s i) (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s (𝓈s [ σ ]𝐸𝑙𝑠))) ⟩
  ob (eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠)) (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s (𝓈s [ σ ]𝐸𝑙𝑠))
    ∎

forget : {Γ Δ : Ctx} → SafeElements Γ Δ → Elements Γ Δ
forget = map𝑇𝑚𝑠 fst

forget[]𝐸𝑙𝑠 : {Γ Δ Σ : Ctx} (𝓈s : SafeElements Δ Σ) (σ :  Ren Γ Δ) →
  forget (𝓈s [ σ ]𝐸𝑙𝑠-S) ≡ forget 𝓈s [ σ ]𝐸𝑙𝑠
forget[]𝐸𝑙𝑠 𝓈s σ = map𝑇𝑚𝑠comp fst _[ σ ]𝐸𝑙-S 𝓈s ∙ map𝑇𝑚𝑠comp _[ σ ]𝐸𝑙 fst 𝓈s ⁻¹ 

{-# TERMINATING #-}
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
  []
    ∷ sub⟨ (λ i → (ιNf (q (eval-⦇α⦈ t (forget[]𝐸𝑙𝑠 𝓈s σ (~ i) ⊕ fst 𝓉))))) ⟩
    ⊙ eval-nat t (𝓈s [ σ ]𝐸𝑙𝑠-S ⊕ 𝓉)
    ∷ sub⟨
      t [ ιNfs (qs (forget (𝓈s [ σ ]𝐸𝑙𝑠-S))) ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ (λ i → t [ ιNfs (qs (forget[]𝐸𝑙𝑠 𝓈s σ i)) ⊕ ιNf (q (fst 𝓉)) ]) ⟩
      t [ ιNfs (qs (forget 𝓈s [ σ ]𝐸𝑙𝑠)) ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ (λ i → t [ ιNfs (qs-nat σ (forget 𝓈s) i) ⊕ ιNf (q (fst 𝓉)) ]) ⟩
      t [ ιNfs (qs (forget 𝓈s) [ σ ]NFS) ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ (λ i → t [ ιNfsLem (qs (forget 𝓈s)) σ i ⊕ ιNf (q (fst 𝓉)) ]) ⟩
      t [ ιNfs (qs (forget 𝓈s)) ∘Tms varify σ ⊕ ιNf (q (fst 𝓉)) ]
        ≡⟨ lem t (ιNfs (qs (forget 𝓈s)) ∘Tms varify σ) (ιNf (q (fst 𝓉))) ⁻¹ ⟩
      t [ W₂Tms _ (ιNfs (qs (forget 𝓈s)) ∘Tms varify σ) ] [ idTms _ ⊕ ιNf (q (fst 𝓉)) ]
        ∎ ⟩
    ∷ ⟨ 𝑂 ⊚ β (t [ W₂Tms _ (ιNfs (qs (forget 𝓈s)) ∘Tms varify σ) ]) (ιNf (q (fst 𝓉))) ⟩⁻¹
    ∷ sub⟨ (λ i → App ([][] (Lam t) (ιNfs (qs (forget 𝓈s))) (varify σ) (~ i)) (ιNf (q (fst 𝓉))) ) ⟩
    ⊙ deepens (𝐴₁ 𝑂 (ιNf (q (fst 𝓉)))) ((invertSteps (eval-nat (Lam t) 𝓈s)) [ varify σ ]𝑆')
    ∷ sub⟨
      App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
        [ W₂Tms _ (varify σ) ])) (ιNf (q (fst 𝓉)))
        ≡⟨ (λ i → App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
          [ Vlem2 σ (~ i) ⊕ 𝑧 ])) (ιNf (q (fst 𝓉))) ) ⟩
      App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
        [ varify (W₂𝑅𝑒𝑛 _ σ) ])) (ιNf (q (fst 𝓉)))
        ≡⟨ (λ i → App (Lam (ιNfLem (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠)
          ⊕ u (VN 𝑧𝑣)))) (W₂𝑅𝑒𝑛 _ σ) (~ i))) (ιNf (q (fst 𝓉)))) ⟩
      App (Lam (ιNf (q (eval-⦇α⦈ t ((forget 𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣)))
        [ W₂𝑅𝑒𝑛 _ σ ]NF))) (ιNf (q (fst 𝓉)))
        ∎ ⟩ ,
    transport
      (λ i → SafeType (eval-⦇α⦈ t (forget[]𝐸𝑙𝑠 𝓈s σ i ⊕ fst 𝓉)))
      (eval-⦇α⦈-safe t (𝓈s [ σ ]𝐸𝑙𝑠-S ⊕ 𝓉))  where
  lem : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (σ : Tms Γ Δ) (s : Tm Γ A) →
          t [ W₂Tms A σ ] [ idTms Γ ⊕ s ] ≡ t [ σ ⊕ s ]
  lem {Γ} {Δ} {A} t σ s =
    t [ W₂Tms A σ ] [ idTms Γ ⊕ s ]
      ≡⟨ [][] t (W₂Tms A σ) (idTms Γ ⊕ s) ⟩
    t [ W₁Tms A σ ∘Tms (idTms Γ ⊕ s) ⊕ s ]
      ≡⟨ (λ i → t [ Wlem1 σ (idTms Γ) s i  ⊕ s ]) ⟩
    t [ σ ∘Tms idTms Γ ⊕ s ]
      ≡⟨ (λ i → t [ ∘TmsIdR σ i ⊕ s ])⟩
    t [ σ ⊕ s ]
      ∎
eval-⦇α⦈-safe {Γ} (App t s) 𝓈s =
  snd (eval-⦇α⦈-safe t 𝓈s (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s (forget 𝓈s) , eval-⦇α⦈-safe s 𝓈s))

eval-nat (V v) 𝓈s =
  [] ∷ sub⟨ (deriveMap ιNf (qs (forget 𝓈s)) v ∙ ap ιNf (deriveMap q (forget 𝓈s) v)) ⁻¹ ⟩
eval-nat {Γ} {A ⇒ B} (Lam t) {Δ} 𝓈s =
  [] ∷
    sub⟨
      (λ i → Lam (ιNf (q (eval-⦇α⦈ t (forget[]𝐸𝑙𝑠 𝓈s (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (~ i) ⊕ u (VN 𝑧𝑣)))))) ⟩
    ⊙ deepens (𝐿 𝑂) (eval-nat t (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠-S ⊕ (u (VN 𝑧𝑣) , u-safe (VN 𝑧𝑣) )))
    ∷ sub⟨
      (λ i → Lam (t [ ιNfs (qs (forget[]𝐸𝑙𝑠 𝓈s (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) i)) ⊕ ιNf (q (u (VN 𝑧𝑣))) ])) ⟩
    ⊙ deepens (𝐿 𝑂) (t [ idParallel (ιNfs (qs (forget 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠)))
      ⊕𝑆 cmp (VN 𝑧𝑣) ]𝑆)
    ∷ sub⟨
      Lam (t [ ιNfs (qs (forget 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠)) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfs (qs-nat (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (forget 𝓈s) i) ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs (forget 𝓈s) [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]NFS) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfsLem (qs (forget 𝓈s)) ( W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) i ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs (forget 𝓈s)) ∘Tms π ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ Wlem5 (ιNfs (qs (forget 𝓈s))) i ⊕ 𝑧 ])) ⟩
      Lam (t [ W₂Tms A (ιNfs (qs (forget 𝓈s))) ])
        ∎ ⟩
eval-nat (App t s) 𝓈s =
  fst (eval-⦇α⦈-safe t 𝓈s (id𝑅𝑒𝑛 _) (eval-⦇α⦈ s (forget 𝓈s) , eval-⦇α⦈-safe s 𝓈s))
    ∷ sub⟨ (λ i → (App (ιNf ([id]NF (q (eval-⦇α⦈ t (forget 𝓈s))) i))
       (ιNf (q (eval-⦇α⦈ s (forget 𝓈s)))))) ⟩
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
forget-us-S (NS ⊕ N) i = forget-us-S NS i ⊕ u N

correctness : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
  Steps t (ιNf (norm t))
correctness {Γ} t =
  []
    ∷ sub⟨
      t
        ≡⟨ [id] t ⁻¹ ⟩
      t [ idTms Γ ]
        ≡⟨ ap (t [_]) (ιidNes Γ ⁻¹) ⟩
      t [ ιNes (idNes Γ) ]
        ∎ ⟩
    ⊙ invertSteps (t [ cmps (idNes Γ) ]𝑆)
    ∷ sub⟨ (λ i → t [ ιNfs (qs (forget-us-S (idNes Γ) (~ i))) ]) ⟩
    ⊙ invertSteps (eval-nat t (us-S (idNes Γ)))
    ∷ sub⟨ (λ i → ιNf (q (eval-⦇α⦈ t (forget-us-S (idNes Γ) i)))) ⟩-}
    
    
