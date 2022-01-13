{-# OPTIONS --cubical #-}

module norm where

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (zero to Z; suc to S)

open import lists
open import syn
open import normal
open import trace

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

q : {Γ : Ctx} {A : Ty} → Element Γ A → Nf Γ A
u : {Γ : Ctx} {A : Ty} → Ne Γ A → Element Γ A

q-nat : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈 : Element Δ A) →
  q (𝓈 [ σ ]𝐸𝑙) ≡ q 𝓈 [ σ ]NF
u-nat : {A : Ty} {Γ Δ : Ctx} (σ : Ren Γ Δ) (N : Ne Δ A) →
  u (N [ σ ]NE) ≡ u N [ σ ]𝐸𝑙

q {A = Base X} 𝓈 = 𝓈
q {Γ} {A ⇒ B} 𝒻 = LAM (q (ob 𝒻 (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) (u (VN 𝑧𝑣))))

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

u-nat {Base x} σ N = refl
u-nat {A ⇒ B} σ N =
  ≡Element⇒ (λ i τ 𝓈 → u (APP ([][]NE N σ τ i) (q 𝓈)))

cmp : {Γ : Ctx} {A : Ty} (N : Ne Γ A) → Steps (ιNf (q (u N))) (ιNe N)
cmp {A = Base s} N = []
cmp {Γ} {A ⇒ B} N =
  deepens (𝐿 𝑂) (cmp (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
    ⊙ deepens (𝐿 (𝐴₂ (ιNe (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE)) 𝑂)) (cmp (VN 𝑧𝑣))
    ∷ sub⟨ (λ i → Lam (App (ιNeLem N (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) i) (V 𝑧𝑣))) ⟩
    ∷ ⟨ 𝑂 ⊚ η (ιNe N) ⟩⁻¹

SafeElement : Ctx → Ty → Set
SafeElement Γ (Base X) = Nf Γ (Base X)
SafeElement Γ (A ⇒ B) =
  Σ (Element Γ (A ⇒ B))
    (λ 𝒻 → (Δ : Ctx) (σ : Ren Δ Γ) (𝓈 : Element Δ A) →
      Steps (ιNf (q (ob 𝒻 σ 𝓈))) (App (ιNf (q 𝒻 [ σ ]NF)) (ιNf (q 𝓈))))

u-safe : {Γ : Ctx} {A : Ty} → Ne Γ A → SafeElement Γ A
u-safe {Γ} {Base c} N = u N
u-safe {Γ} {A ⇒ B} N = u N ,
  λ Δ σ 𝓈 →
    cmp (APP (N [ σ ]NE) (q 𝓈))
      ∷ sub⟨ (λ i → (App (ιNeLem N σ i) (ιNf (q 𝓈)))) ⟩
      ⊙ deepens (𝐴₁ 𝑂 (ιNf (q 𝓈))) (invertSteps (cmp N) [ varify σ ]𝑆')
      ∷ sub⟨
        App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
          [ W₂Tms A (varify σ) ])) (ιNf (q 𝓈))
          ≡⟨ (λ i → App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
            [ Vlem2 σ (~ i) ⊕ 𝑧 ])) (ιNf (q 𝓈))) ⟩
        App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
          [ varify (W₂𝑅𝑒𝑛 A σ) ])) (ιNf (q 𝓈))
          ≡⟨ (λ i → App (Lam (ιNfLem (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣))))))
            (W₂𝑅𝑒𝑛 A σ) (~ i))) (ιNf (q 𝓈))) ⟩
        App (Lam (ιNf (q (u (APP (N [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ) ]NE) (q (u (VN 𝑧𝑣)))))
          [ W₂𝑅𝑒𝑛 A σ ]NF))) (ιNf (q 𝓈))
          ∎ ⟩

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

qs-nat : {Σ : Ctx} {Γ Δ : Ctx} (σ : Ren Γ Δ) (𝓈s : Elements Δ Σ) →
  qs (𝓈s [ σ ]𝐸𝑙𝑠) ≡ qs 𝓈s [ σ ]NFS
qs-nat σ ! = refl
qs-nat σ (𝓈s ⊕ 𝓈) i = qs-nat σ 𝓈s i ⊕ q-nat σ 𝓈 i

eval-⦇α⦈ : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Elements Γ Δ → Element Γ A
eval-⦇α⦈-hom : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Ren Γ Δ) (𝓈s : Elements Δ Σ) →
  eval-⦇α⦈ t 𝓈s [ σ ]𝐸𝑙 ≡ eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠)

eval-⦇α⦈ (V v) 𝓈s = derive 𝓈s v
eval-⦇α⦈ (Lam t) 𝓈s =
  nat
    (λ σ 𝓉 → eval-⦇α⦈ t (𝓈s [ σ ]𝐸𝑙𝑠 ⊕ 𝓉))
    (λ σ τ 𝓈 →
      {!eval-⦇α⦈ t (𝓈s [ τ ]𝐸𝑙𝑠 ⊕ 𝓈) [ σ ]𝐸𝑙 !})
eval-⦇α⦈ {Γ} (App t s) 𝓈s =
  ob (eval-⦇α⦈ t 𝓈s) (id𝑅𝑒𝑛 Γ) (eval-⦇α⦈ s 𝓈s)

eval-⦇α⦈-hom (V v) σ 𝓈s = {!!}
eval-⦇α⦈-hom (Lam t) σ 𝓈s = {!!}
eval-⦇α⦈-hom (App t t₁) σ 𝓈s = {!!}

eval-nat : {Γ : Ctx} {A : Ty} (t : Tm Γ A) {Δ : Ctx} (𝓈s : Elements Δ Γ) →
  Steps (ιNf (q (eval-⦇α⦈ t 𝓈s))) (t [ ιNfs (qs 𝓈s) ])
eval-⦇α⦈-safe : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (𝓈s : Elements Γ Δ) →
  SafeElement Γ (A ⇒ B)

eval-nat (V v) 𝓈s =
  [] ∷ sub⟨ ap ιNf (deriveMap q 𝓈s v) ⁻¹ ∙ deriveMap ιNf (qs 𝓈s) v ⁻¹ ⟩
eval-nat {Γ} {A ⇒ B} (Lam t) {Δ} 𝓈s =
  deepens (𝐿 𝑂) (eval-nat t (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠 ⊕ u (VN 𝑧𝑣)))
    ⊙ deepens (𝐿 𝑂) (t [ idParallel (ιNfs (qs (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠))) ⊕𝑆 cmp (VN 𝑧𝑣) ]𝑆)
    ∷ sub⟨
      Lam (t [ ιNfs (qs (𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]𝐸𝑙𝑠)) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfs (qs-nat (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) 𝓈s i) ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs 𝓈s [ W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ]NFS) ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ ιNfsLem (qs 𝓈s) ( W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) i ⊕ 𝑧 ])) ⟩
      Lam (t [ ιNfs (qs 𝓈s) ∘Tms π ⊕ 𝑧 ])
        ≡⟨ (λ i → Lam (t [ Wlem5 (ιNfs (qs 𝓈s)) i ⊕ 𝑧 ])) ⟩
      Lam (t [ W₂Tms A (ιNfs (qs 𝓈s)) ])
        ∎ ⟩
eval-nat (App t s) 𝓈s =
  {!eval-⦇α⦈-safe  !}

eval-⦇α⦈-safe t 𝓈s =
  (eval-⦇α⦈ (Lam t) 𝓈s) ,
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

idA⇒A = 𝐼𝑑 (Base 'A' ⇒ Base 'A')
