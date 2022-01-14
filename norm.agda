{-# OPTIONS --cubical #-}

module norm where

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (zero to Z; suc to S)

open import lists
open import syn
open import normal
open import trace

data ⊤ : Type where
  tt : ⊤

Element : Ctx → Ty → Set
_[_]𝐸𝑙 : {Γ Δ : Ctx} {A : Ty} → Element Δ A → Ren Γ Δ → Element Γ A

-- ob sets of semantic presheaf

{-# NO_POSITIVITY_CHECK #-}
record Element⇒ (Γ : Ctx) (A B : Ty) : Type where
  inductive
  pattern
  constructor nat
  field
    ob : {Δ : Ctx} → Ren Δ Γ → Element Δ A → Element Δ B
    hom : {Δ Σ : Ctx} (σ : Ren Δ Σ) (τ : Ren Σ Γ) (𝓈 : Element Σ A) →
      (ob τ 𝓈 [ σ ]𝐸𝑙 ≡ ob (τ ∘𝑅𝑒𝑛 σ) (𝓈 [ σ ]𝐸𝑙))
      
Element Γ (Base X) = Nf Γ (Base X)
Element Γ (A ⇒ B) = Element⇒ Γ A B

open Element⇒

postulate
  ≡Element⇒ : {Γ : Ctx} {A B : Ty} {𝒻 ℊ : Element⇒ Γ A B} →
    Path ({Δ : Ctx} → Ren Δ Γ → Element Δ A → Element Δ B) (ob 𝒻) (ob ℊ) → 𝒻 ≡ ℊ

infix 30 _[_]𝐸𝑙
_[_]𝐸𝑙 {A = Base x} 𝓈 σ = 𝓈 [ σ ]NF
_[_]𝐸𝑙 {A = A ⇒ B} 𝒻 σ =
  nat
    (λ τ 𝓈 → (ob 𝒻) (σ ∘𝑅𝑒𝑛 τ) 𝓈)
    (λ τ μ 𝓈 →
      ob 𝒻 (σ ∘𝑅𝑒𝑛 μ) 𝓈 [ τ ]𝐸𝑙
        ≡⟨ hom 𝒻 τ (σ ∘𝑅𝑒𝑛 μ) 𝓈 ⟩
      ob 𝒻 (σ ∘𝑅𝑒𝑛 μ ∘𝑅𝑒𝑛 τ) (𝓈 [ τ ]𝐸𝑙)
        ≡⟨ (λ i → ob 𝒻 (∘𝑅𝑒𝑛Assoc σ μ τ i) (𝓈 [ τ ]𝐸𝑙)) ⟩
      ob 𝒻 (σ ∘𝑅𝑒𝑛 (μ ∘𝑅𝑒𝑛 τ)) (𝓈 [ τ ]𝐸𝑙)
        ∎)

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

Elements = 𝑇𝑚𝑠 Element
SafeElements = 𝑇𝑚𝑠 SafeElement

qs : {Γ Δ : Ctx} → Elements Γ Δ → Nfs Γ Δ
qs = map𝑇𝑚𝑠 q

us : {Γ Δ : Ctx} → Nes Γ Δ → Elements Γ Δ
us = map𝑇𝑚𝑠 u

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

eval-nat : {Γ : Ctx} {A : Ty} (t : Tm Γ A) {Δ : Ctx} (𝓈s : SafeElements Δ Γ) →
  Steps (ιNf (q (eval-⦇α⦈ t (forget 𝓈s)))) (t [ ιNfs (qs (forget 𝓈s)) ])

eval-⦇α⦈-safe : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (𝓈s : SafeElements Γ Δ) →
  SafeType (eval-⦇α⦈ t (forget 𝓈s))
eval-⦇α⦈-safe (V v) 𝓈s =
  transport (λ i → SafeType (deriveMap {tm₂ = Element} fst 𝓈s v (~ i))) (snd (derive 𝓈s v))
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


{-_[_]𝐸𝑙safe {A = Base c} (N , tt) σ = N [ σ ]𝐸𝑙 , tt
_[_]𝐸𝑙safe {A = A ⇒ B} 𝓉 σ =
  (fst 𝓉 [ σ ]𝐸𝑙) ,
    (λ τ 𝓈 →
      snd 𝓉 (σ ∘𝑅𝑒𝑛 τ) 𝓈
        ∷ sub⟨
          App (ιNf (q (fst 𝓉) [ σ ∘𝑅𝑒𝑛 τ ]NF)) (ιNf (q-safe 𝓈))
            ≡⟨ (λ i → App (ιNf ([][]NF (q (fst 𝓉)) σ τ (~ i))) (ιNf (q-safe  𝓈))) ⟩
          App (ιNf (q (fst 𝓉) [ σ ]NF [ τ ]NF)) (ιNf (q-safe 𝓈))
            ≡⟨ (λ i → App (ιNf (q-nat σ (fst 𝓉) (~ i) [ τ ]NF)) (ιNf (q-safe 𝓈))) ⟩
          App (ιNf (q (fst 𝓉 [ σ ]𝐸𝑙) [ τ ]NF)) (ιNf (q-safe 𝓈))
            ∎ ⟩)-}

{-q-safe : {Γ : Ctx} {A : Ty} → SafeElement Γ A → Nf Γ A
q-safe 𝓈 = q (fst 𝓈)

Elements = 𝑇𝑚𝑠 Element
SafeElements = 𝑇𝑚𝑠 SafeElement

qs : {Γ Δ : Ctx} → Elements Γ Δ → Nfs Γ Δ
qs = map𝑇𝑚𝑠 q

us : {Γ Δ : Ctx} → Nes Γ Δ → Elements Γ Δ
us = map𝑇𝑚𝑠 u

qs-safe : {Γ Δ : Ctx} → SafeElements Γ Δ → Nfs Γ Δ
qs-safe = map𝑇𝑚𝑠 q-safe

us-safe : {Γ Δ : Ctx} → Nes Γ Δ → SafeElements Γ Δ
us-safe = map𝑇𝑚𝑠 u-safe

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

qs-nat : {Σ : Ctx} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈s : Elements Δ Σ) →
  qs (𝓈s [ σ ]𝐸𝑙𝑠) ≡ qs 𝓈s [ σ ]NFS
qs-nat σ ! = refl
qs-nat σ (𝓈s ⊕ 𝓈) i = qs-nat σ 𝓈s i ⊕ q-nat σ 𝓈 i



forget : {Γ Δ : Ctx} → SafeElements Γ Δ → Elements Γ Δ
forget = map𝑇𝑚𝑠 fst

eval-⦇α⦈' : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → SafeElements Γ Δ → Element Γ A
eval-⦇α⦈' t 𝓈s = eval-⦇α⦈ t (forget 𝓈s)

eval-⦇α⦈-safe : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (𝓈s : SafeElements Γ Δ) →
  SafeType (eval-⦇α⦈' t 𝓈s)

eval-nat : {Γ : Ctx} {A : Ty} (t : Tm Γ A) {Δ : Ctx} (𝓈s : SafeElements Δ Γ) →
  Steps (ιNf (q (eval-⦇α⦈' t 𝓈s))) (t [ ιNfs (qs-safe 𝓈s) ])

infix 30 _[_]𝐸𝑙safe
_[_]𝐸𝑙safe : {Γ Δ : Ctx} {A : Ty} → SafeElement Δ A → Ren Γ Δ → SafeElement Γ A
_[_]𝐸𝑙safe {A = Base c} (N , tt) σ = N [ σ ]𝐸𝑙 , tt
_[_]𝐸𝑙safe {A = A ⇒ B} 𝓉 σ =
  (fst 𝓉 [ σ ]𝐸𝑙) ,
    (λ τ 𝓈 →
      snd 𝓉 (σ ∘𝑅𝑒𝑛 τ) 𝓈
        ∷ sub⟨
          App (ιNf (q (fst 𝓉) [ σ ∘𝑅𝑒𝑛 τ ]NF)) (ιNf (q-safe 𝓈))
            ≡⟨ (λ i → App (ιNf ([][]NF (q (fst 𝓉)) σ τ (~ i))) (ιNf (q-safe  𝓈))) ⟩
          App (ιNf (q (fst 𝓉) [ σ ]NF [ τ ]NF)) (ιNf (q-safe 𝓈))
            ≡⟨ (λ i → App (ιNf (q-nat σ (fst 𝓉) (~ i) [ τ ]NF)) (ιNf (q-safe 𝓈))) ⟩
          App (ιNf (q (fst 𝓉 [ σ ]𝐸𝑙) [ τ ]NF)) (ιNf (q-safe 𝓈))
            ∎ ⟩)

forget[]𝐸𝑙 : {Γ Δ : Ctx} {A : Ty} (𝓈 : SafeElement Δ A) (σ :  Ren Γ Δ) →
  fst (𝓈 [ σ ]𝐸𝑙safe) ≡ fst 𝓈 [ σ ]𝐸𝑙
forget[]𝐸𝑙 {A = Base C} (𝓈 , tt) σ = refl
forget[]𝐸𝑙 {A = A ⇒ B} 𝓈 σ = refl

infix 30 _[_]𝐸𝑙𝑠safe
_[_]𝐸𝑙𝑠safe : {Γ Δ Σ : Ctx} → SafeElements Δ Σ → Ren Γ Δ → SafeElements Γ Σ
𝓈s [ σ ]𝐸𝑙𝑠safe = map𝑇𝑚𝑠 _[ σ ]𝐸𝑙safe 𝓈s

forget[]𝐸𝑙𝑠 : {Γ Δ Σ : Ctx} (𝓈s : SafeElements Δ Σ) (σ :  Ren Γ Δ) →
  forget (𝓈s [ σ ]𝐸𝑙𝑠safe) ≡ forget 𝓈s [ σ ]𝐸𝑙𝑠
forget[]𝐸𝑙𝑠 ! σ = refl
forget[]𝐸𝑙𝑠 (𝓈s ⊕ 𝓈) σ i = forget[]𝐸𝑙𝑠 𝓈s σ i ⊕ forget[]𝐸𝑙 𝓈 σ i

q-nat-safe : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈 : SafeElement Δ A) →
  q-safe (𝓈 [ σ ]𝐸𝑙safe) ≡ q-safe 𝓈 [ σ ]NF
{-u-nat-safe : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (N : Ne Δ A) →
  u-safe (N [ σ ]NE) ≡ u-safe N [ σ ]𝐸𝑙safe-}

q-nat-safe {Base c} σ (𝓈 , tt) = refl
q-nat-safe {A ⇒ B} σ 𝓈 = q-nat σ (fst 𝓈)

{-u-nat-safe {Base c} σ N = refl
u-nat-safe {A ⇒ B} σ N = ≡SafeElement (u-nat σ N)-}

qs-nat-safe : {Γ Δ Σ : Ctx} (σ : Ren Γ Δ) (𝓈s : SafeElements Δ Σ) →
  qs-safe (𝓈s [ σ ]𝐸𝑙𝑠safe) ≡ qs-safe 𝓈s [ σ ]NFS
qs-nat-safe σ ! = refl
qs-nat-safe σ (𝓈s ⊕ 𝓈) i = qs-nat-safe σ 𝓈s i ⊕ q-nat-safe σ 𝓈 i



eval-nat (V v) 𝓈s =
  [] ∷ sub⟨ {!ap ιNf (deriveMap q (forget 𝓈s) v) ⁻¹ ∙ deriveMap {tm₂ = Tm} ιNf (qs-safe 𝓈s) v ⁻¹!} ⟩
eval-nat {Γ} {A ⇒ B} (Lam t) {Δ} 𝓈s =
  {!deepens (𝐿 𝑂) (eval-nat t (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠safe ⊕ u-safe (VN 𝑧𝑣)))
    {-⊙ deepens (𝐿 𝑂) (t [ idParallel (ιNfs (qs (forgetsSafe 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠))) ⊕𝑆 cmp (VN 𝑧𝑣) ]𝑆)
    ∷ sub⟨
      Lam (t [ ιNfs (qs (forgetsSafe 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠)) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfs (qs-nat (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (forgetsSafe 𝓈s) i) ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs (forgetsSafe 𝓈s) [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]NFS) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfsLem (qs (forgetsSafe 𝓈s)) ( W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) i ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs (forgetsSafe 𝓈s)) ∘Tms π ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ Wlem5 (ιNfs (qs (forgetsSafe 𝓈s))) i ⊕ 𝑧 ])) ⟩
      Lam (t [ W₂Tms A (ιNfs (qs (forgetsSafe 𝓈s))) ])
        ∎ ⟩-}!}
eval-nat (App t s) 𝓈s =
  {!eval-⦇α⦈-safe t !}


idNes : (Γ : Ctx) → Nes Γ Γ
idNes Γ = map𝑇𝑚𝑠 VN (id𝑅𝑒𝑛 Γ)

ιidNes : (Γ : Ctx) → ιNes (idNes Γ) ≡ idTms Γ
ιidNes ∅ = refl
ιidNes (Γ ⊹ A) = ap (_⊕ 𝑧) (map𝑇𝑚𝑠comp ιNe VN (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)))

forget-u-safe : {Γ : Ctx} {A : Ty} (N : Ne Γ A) →
  fst (u-safe N) ≡ u N
forget-u-safe {A = Base c} N = refl
forget-u-safe {A = A ⇒ B} N = refl

forget-us-safe : {Γ Δ : Ctx} (NS : Nes Γ Δ) →
  forget (us-safe NS) ≡ us NS
forget-us-safe ! = refl
forget-us-safe (NS ⊕ N) i = forget-us-safe NS i ⊕ forget-u-safe N i

norm : {Γ : Ctx} {A : Ty} → Tm Γ A → Nf Γ A
norm {Γ} t = q (eval-⦇α⦈ t (us (idNes Γ)))

correctness : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
  Steps (ιNf (norm t)) t
correctness {Γ} t =
  {![]
    ∷ sub⟨ (λ i → ιNf (q (eval-⦇α⦈ t (map𝑇𝑚𝑠comp fst u-safe (idNes Γ) i)))) ⟩
    --⊙ eval-nat t (us-safe (idNes Γ))
    {-⊙ (t [ cmps (idNes Γ) ]𝑆)
    ∷ sub⟨
      t [ ιNes (idNes Γ) ]
        ≡⟨ ap (t [_]) (ιidNes Γ) ⟩
      t [ idTms Γ ]
        ≡⟨ [id] t ⟩
      t
        ∎ ⟩-}!}

-- Tests

ChurchType : Ty → Ty
ChurchType A = (A ⇒ A) ⇒ A ⇒ A

ChurchBody : {Γ : Ctx} {A : Ty} → ℕ → Tm (Γ ⊹ (A ⇒ A) ⊹ A) A
ChurchBody Z = (V 𝑧𝑣)
ChurchBody (S n) = App (V (𝑠𝑣 𝑧𝑣)) (ChurchBody n)

𝐶𝑁𝑢𝑚 : {Γ : Ctx} {A : Ty} → ℕ → Tm Γ (ChurchType A)
𝐶𝑁𝑢𝑚 n = Lam (Lam (ChurchBody n))

PlusType : Ty → Ty
PlusType A = ChurchType A ⇒ ChurchType A ⇒ ChurchType A

Plus : {Γ : Ctx} {A : Ty} → Tm Γ (PlusType A)
Plus = Lam (Lam (Lam (Lam (App (App (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣)))) (V (𝑠𝑣 𝑧𝑣)))
                               (App (App (V (𝑠𝑣 (𝑠𝑣 𝑧𝑣))) (V (𝑠𝑣 𝑧𝑣))) (V 𝑧𝑣))))))

𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 : (A : Ty) → ℕ → ℕ → Tm ∅ (ChurchType A)
𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 A n m = App (App Plus (𝐶𝑁𝑢𝑚 n)) (𝐶𝑁𝑢𝑚 m)

sum = 𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 (Base 'A') 2 2

𝐼𝑑 : (A : Ty) → Tm ∅ (A ⇒ A)
𝐼𝑑 A = Lam (V 𝑧𝑣)

idA⇒A = 𝐼𝑑 (Base 'A' ⇒ Base 'A')-}

{-{-forgetSafe : {Γ : Ctx} {A : Ty} → SafeElement Γ A → Element Γ A
forgetSafe {Γ} {Base c} N = N
forgetSafe {Γ} {A ⇒ B} 𝓈 = fst 𝓈

forgetsSafe : {Γ Δ : Ctx} → SafeElements Γ Δ → Elements Γ Δ
forgetsSafe = map𝑇𝑚𝑠 forgetSafe-}

{-eval-⦇α⦈-safe : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (𝓈s : SafeElements Γ Δ) →
  {Δ : Ctx} (σ : Ren Δ Γ) (𝓉 : Element Δ A) →
      Steps (ιNf (q (ob (eval-⦇α⦈ t (forgetsSafe 𝓈s)) σ 𝓉)))
            (App (ιNf (q (eval-⦇α⦈ t (forgetsSafe 𝓈s)) [ σ ]NF)) (ιNf (q 𝓉)))-}
{-eval-nat : {Γ : Ctx} {A : Ty} (t : Tm Γ A) {Δ : Ctx} (𝓈s : SafeElements Δ Γ) →
  Steps (ιNf (q-safe (eval-⦇α⦈-safe t 𝓈s))) (t [ ιNfs (qs-safe  𝓈s) ])

_[_]𝐸𝑙safe : {Γ Δ : Ctx} {A : Ty} → SafeElement Δ A → Ren Γ Δ → SafeElement Γ A
_[_]𝐸𝑙safe {A = Base c} t σ = t [ σ ]𝐸𝑙
_[_]𝐸𝑙safe {A = A ⇒ B} t σ =
  (fst t [ σ ]𝐸𝑙) ,
    (λ τ 𝓈 →
      snd t (σ ∘𝑅𝑒𝑛 τ) 𝓈
        ∷ sub⟨
          App (ιNf (q (fst t) [ σ ∘𝑅𝑒𝑛 τ ]NF)) (ιNf (q 𝓈))
            ≡⟨ (λ i → App (ιNf ([][]NF (q (fst t)) σ τ (~ i))) (ιNf (q 𝓈))) ⟩
          App (ιNf (q (fst t) [ σ ]NF [ τ ]NF)) (ιNf (q 𝓈))
            ≡⟨ (λ i → App (ιNf (q-nat σ (fst t) (~ i) [ τ ]NF)) (ιNf (q 𝓈))) ⟩
          App (ιNf (q (fst t [ σ ]𝐸𝑙) [ τ ]NF)) (ιNf (q 𝓈))
            ∎ ⟩)
          {-App (Lam (ιNf (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣)))
            [ W₂𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ) ]NF))) (ιNf (q 𝓈))
            ≡⟨ (λ i → App (Lam (ιNf (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣)))
              [ Wlem4𝑅𝑒𝑛 σ τ (~ i) ]NF))) (ιNf (q 𝓈))) ⟩
          App (Lam (ιNf (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣)))
            [ W₂𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))
            ≡⟨ (λ i → App (Lam (ιNf ([][]NF (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣))))
              (W₂𝑅𝑒𝑛 A σ) (W₂𝑅𝑒𝑛 A τ) (~ i)))) (ιNf (q 𝓈))) ⟩
          App (Lam (ιNf (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣)))
            [ W₂𝑅𝑒𝑛 A σ ]NF [ W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))
            ≡⟨ (λ i → App (Lam (ιNf (q-nat (W₂𝑅𝑒𝑛 A σ)
              (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣))) (~ i) [ W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))) ⟩
          App (Lam (ιNf (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣))
            [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙) [ W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))
            ≡⟨ (λ i → App (Lam (ιNf (q (hom (fst t) (W₂𝑅𝑒𝑛 A σ) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _)) (u (VN 𝑧𝑣)) i)
              [ W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))) ⟩
          App (Lam (ιNf (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A σ) (u (VN 𝑧𝑣)
            [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)) [ W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))
            ≡⟨ (λ i → App (Lam (ιNf (q (ob (fst t) (Wlem5𝑅𝑒𝑛 (id𝑅𝑒𝑛 _) σ i) (u (VN 𝑧𝑣)
              [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)) [ W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))) ⟩
          App (Lam (ιNf (q (ob (fst t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 _ ∘𝑅𝑒𝑛 σ)) (u (VN 𝑧𝑣)
            [ W₂𝑅𝑒𝑛 A σ ]𝐸𝑙)) [ W₂𝑅𝑒𝑛 A τ ]NF))) (ιNf (q 𝓈))
            ≡⟨
            ∎-}

_[_]𝐸𝑙𝑠safe : {Γ Δ Σ : Ctx} → SafeElements Δ Σ → Ren Γ Δ → SafeElements Γ Σ
𝓈s [ σ ]𝐸𝑙𝑠safe = map𝑇𝑚𝑠 _[ σ ]𝐸𝑙safe 𝓈s

{-eval-⦇α⦈-safe (V v) 𝓈s = derive 𝓈s v
eval-⦇α⦈-safe (Lam t) 𝓈s =
  (eval-⦇α⦈ (Lam t) (forgetsSafe 𝓈s)) ,
    {!!}
eval-⦇α⦈-safe {Γ} (App t s) 𝓈s =
  {!ob (eval-⦇α⦈-safe t 𝓈s) (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈-safe s 𝓈s)!}-}-}

{-eval-nat (V v) 𝓈s =
  [] ∷ sub⟨ ap ιNf (deriveMap q (forgetsSafe 𝓈s) v) ⁻¹ ∙ deriveMap ιNf (qs-safe 𝓈s) v ⁻¹ ⟩
eval-nat {Γ} {A ⇒ B} (Lam t) {Δ} 𝓈s =
  {!deepens (𝐿 𝑂) (eval-nat t (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠safe ⊕ u-safe (VN 𝑧𝑣)))
    {-⊙ deepens (𝐿 𝑂) (t [ idParallel (ιNfs (qs (forgetsSafe 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠))) ⊕𝑆 cmp (VN 𝑧𝑣) ]𝑆)
    ∷ sub⟨
      Lam (t [ ιNfs (qs (forgetsSafe 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠)) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfs (qs-nat (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) (forgetsSafe 𝓈s) i) ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs (forgetsSafe 𝓈s) [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]NFS) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfsLem (qs (forgetsSafe 𝓈s)) ( W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) i ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs (forgetsSafe 𝓈s)) ∘Tms π ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ Wlem5 (ιNfs (qs (forgetsSafe 𝓈s))) i ⊕ 𝑧 ])) ⟩
      Lam (t [ W₂Tms A (ιNfs (qs (forgetsSafe 𝓈s))) ])
        ∎ ⟩-}!}
eval-nat (App t s) 𝓈s =
  {!eval-⦇α⦈-safe t !}-}

{-eval-⦇α⦈-safe (V v) 𝓈s = derive 𝓈s v
eval-⦇α⦈-safe (Lam t) 𝓈s =
  (eval-⦇α⦈ (Lam t) (map𝑇𝑚𝑠 fst 𝓈s)) ,
    (λ Σ σ 𝓉 →
      eval-nat t (𝓈s [ σ ]𝐸𝑙𝑠 ⊕ 𝓉)
        ∷ sub⟨
          t [ ιNfs (qs (𝓈s [ σ ]𝐸𝑙𝑠)) ⊕ ιNf (q 𝓉) ]
            ≡⟨ (λ i → t [ ιNfs (qs-nat σ 𝓈s i) ⊕ ιNf (q 𝓉) ]) ⟩
          t [ ιNfs (qs 𝓈s [ σ ]NFS) ⊕ ιNf (q 𝓉) ]
            ≡⟨ (λ i → t [ ιNfsLem (qs 𝓈s) σ i ⊕ ιNf (q 𝓉) ]) ⟩
          t [ ιNfs (qs 𝓈s) ∘Tms varify σ ⊕ ιNf (q 𝓉) ]
            ≡⟨ lem t (ιNfs (qs 𝓈s) ∘Tms varify σ) (ιNf (q 𝓉)) ⁻¹ ⟩
          t [ W₂Tms _ (ιNfs (qs 𝓈s) ∘Tms varify σ) ] [ idTms Σ ⊕ ιNf (q 𝓉) ]
            ≡⟨ (λ i → t [ Wlem4 (ιNfs (qs 𝓈s)) (varify σ) (~ i) ] [ idTms Σ ⊕ ιNf (q 𝓉) ]) ⟩
          t [ W₂Tms _ (ιNfs (qs 𝓈s)) ∘Tms W₂Tms _ (varify σ) ] [ idTms Σ ⊕ ιNf (q 𝓉) ]
            ≡⟨ (λ i → [][] t (W₂Tms _ (ιNfs (qs 𝓈s))) (W₂Tms _ (varify σ)) (~ i)
              [ idTms Σ ⊕ ιNf (q 𝓉) ]) ⟩
          t [ W₂Tms _ (ιNfs (qs 𝓈s)) ] [ W₂Tms _ (varify σ) ] [ idTms Σ ⊕ ιNf (q 𝓉) ]
            ∎ ⟩
        ∷ ⟨ 𝑂 ⊚ β (t [ W₂Tms _ (ιNfs (qs 𝓈s)) ] [ W₂Tms _ (varify σ) ]) (ιNf (q 𝓉)) ⟩⁻¹
        ⊙ deepens (𝐴₁ 𝑂 (ιNf (q 𝓉))) ((invertSteps (eval-nat (Lam t) 𝓈s)) [ varify σ ]𝑆')
        ∷ sub⟨
          App (Lam (ιNf (q (eval-⦇α⦈ t ((𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
            [ W₂Tms _ (varify σ) ])) (ιNf (q 𝓉))
            ≡⟨ (λ i → App (Lam (ιNf (q (eval-⦇α⦈ t ((𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
              [ Vlem2 σ (~ i) ⊕ 𝑧 ])) (ιNf (q 𝓉)) ) ⟩
          App (Lam (ιNf (q (eval-⦇α⦈ t ((𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
            [ varify (W₂𝑅𝑒𝑛 _ σ) ])) (ιNf (q 𝓉))
            ≡⟨ (λ i → App (Lam (ιNfLem (q (eval-⦇α⦈ t ((𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣))))
              (W₂𝑅𝑒𝑛 _ σ) (~ i))) (ιNf (q 𝓉))) ⟩
          App (Lam (ιNf (q (eval-⦇α⦈ t ((𝓈s [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝐸𝑙𝑠) ⊕ u (VN 𝑧𝑣)))
            [ W₂𝑅𝑒𝑛 _ σ ]NF))) (ιNf (q 𝓉))
            ∎ ⟩) where
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
      
eval-⦇α⦈-safe (App t t₁) 𝓈s = {!!}

{-eval-⦇α⦈-safe t 𝓈s =
  ∎-}

idNes : (Γ : Ctx) → Nes Γ Γ
idNes Γ = map𝑇𝑚𝑠 VN (id𝑅𝑒𝑛 Γ)

ιidNes : (Γ : Ctx) → ιNes (idNes Γ) ≡ idTms Γ
ιidNes ∅ = refl
ιidNes (Γ ⊹ A) = ap (_⊕ 𝑧) (map𝑇𝑚𝑠comp ιNe VN (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)))

norm : {Γ : Ctx} {A : Ty} → Tm Γ A → Nf Γ A
norm {Γ} t = q (eval-⦇α⦈ t (us (idNes Γ)))

correctness : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
  Steps (ιNf (norm t)) t
correctness {Γ} t =
  eval-nat t (us (idNes Γ))
    ⊙ (t [ cmps (idNes Γ) ]𝑆)
    ∷ sub⟨
      t [ ιNes (idNes Γ) ]
        ≡⟨ ap (t [_]) (ιidNes Γ) ⟩
      t [ idTms Γ ]
        ≡⟨ [id] t ⟩
      t
        ∎ ⟩

-- Tests

ChurchType : Ty → Ty
ChurchType A = (A ⇒ A) ⇒ A ⇒ A

ChurchBody : {Γ : Ctx} {A : Ty} → ℕ → Tm (Γ ⊹ (A ⇒ A) ⊹ A) A
ChurchBody Z = (V 𝑧𝑣)
ChurchBody (S n) = App (V (𝑠𝑣 𝑧𝑣)) (ChurchBody n)

𝐶𝑁𝑢𝑚 : {Γ : Ctx} {A : Ty} → ℕ → Tm Γ (ChurchType A)
𝐶𝑁𝑢𝑚 n = Lam (Lam (ChurchBody n))

PlusType : Ty → Ty
PlusType A = ChurchType A ⇒ ChurchType A ⇒ ChurchType A

Plus : {Γ : Ctx} {A : Ty} → Tm Γ (PlusType A)
Plus = Lam (Lam (Lam (Lam (App (App (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣)))) (V (𝑠𝑣 𝑧𝑣)))
                               (App (App (V (𝑠𝑣 (𝑠𝑣 𝑧𝑣))) (V (𝑠𝑣 𝑧𝑣))) (V 𝑧𝑣))))))

𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 : (A : Ty) → ℕ → ℕ → Tm ∅ (ChurchType A)
𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 A n m = App (App Plus (𝐶𝑁𝑢𝑚 n)) (𝐶𝑁𝑢𝑚 m)

sum = 𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 (Base 'A') 2 2

𝐼𝑑 : (A : Ty) → Tm ∅ (A ⇒ A)
𝐼𝑑 A = Lam (V 𝑧𝑣)

idA⇒A = 𝐼𝑑 (Base 'A' ⇒ Base 'A')-}-}
