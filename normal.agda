{-# OPTIONS --cubical #-}

module normal where

open import lists
open import syn

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

[id]NE : {Γ : Ctx} {A : Ty} → (M : Ne Γ A) →
  M [ id𝑅𝑒𝑛 Γ ]NE ≡ M
[id]NF : {Γ : Ctx} {A : Ty} → (N : Nf Γ A) →
  N [ id𝑅𝑒𝑛 Γ ]NF ≡ N

[id]NE (VN 𝑧𝑣) = refl
[id]NE (VN (𝑠𝑣 v)) =
  VN (v [ W₁𝑅𝑒𝑛 _ (id𝑅𝑒𝑛 _) ]𝑅)
    ≡⟨ ap VN (Wlem2𝑅𝑒𝑛 v (id𝑅𝑒𝑛 _)) ⟩
  VN (𝑠𝑣 (v [ id𝑅𝑒𝑛 _ ]𝑅))
    ≡⟨ ap VN (ap 𝑠𝑣 ([id]𝑅𝑒𝑛 v)) ⟩
  VN (𝑠𝑣 v)
    ∎
[id]NE (APP M N) i = APP ([id]NE M i) ([id]NF N i)

[id]NF (NEU M) = ap NEU ([id]NE M)
[id]NF (LAM N) = ap LAM ([id]NF N)

[][]NE : {Γ Δ Σ : Ctx} {A : Ty} (M : Ne Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  M [ σ ]NE [ τ ]NE ≡ M [ σ ∘𝑅𝑒𝑛 τ ]NE
[][]NF : {Γ Δ Σ : Ctx} {A : Ty} (N : Nf Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  N [ σ ]NF [ τ ]NF ≡ N [ σ ∘𝑅𝑒𝑛 τ ]NF

[][]NE (VN v) σ τ = ap VN ([][]𝑅𝑒𝑛 v σ τ)
[][]NE (APP M N) σ τ i = APP ([][]NE M σ τ i) ([][]NF N σ τ i)

[][]NF (NEU M) σ τ = ap NEU ([][]NE M σ τ)
[][]NF (LAM N) σ τ =
  LAM (N [ W₂𝑅𝑒𝑛 _ σ ]NF [ W₂𝑅𝑒𝑛 _ τ ]NF)
    ≡⟨ ap LAM ([][]NF N (W₂𝑅𝑒𝑛 _ σ) (W₂𝑅𝑒𝑛 _ τ) ) ⟩
  LAM (N [ W₂𝑅𝑒𝑛 _ σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 _ τ ]NF)
    ≡⟨ (λ i → LAM (N [ Wlem4𝑅𝑒𝑛 σ τ i ]NF)) ⟩
  LAM (N [ W₂𝑅𝑒𝑛 _ (σ ∘𝑅𝑒𝑛 τ) ]NF)
    ∎

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
