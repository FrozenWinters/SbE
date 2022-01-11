{-# OPTIONS --cubical #-}

module norm where

open import Cubical.Data.Sigma

open import lists
open import syn
open import trace


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

SafeElement : Ctx → Ty → Set
SafeElement Γ (Base X) = Nf Γ (Base X)
SafeElement Γ (A ⇒ B) =
  Σ (Element Γ (A ⇒ B))
    (λ 𝒻 → (Δ : Ctx) (σ : Ren Δ Γ) (𝓈 : Element Δ A) →
      Steps (ιNf (q (𝒻 σ 𝓈))) (App (ιNf (q 𝒻 [ σ ]NF)) (ιNf (q 𝓈))))

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
