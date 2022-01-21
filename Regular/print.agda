module print where

open import lists
open import syn
open import trace

open import Data.String public
open import Agda.Builtin.String using () renaming (primShowNat to showNat)
open import Data.Nat renaming (zero to Z; suc to S)

infixl 20 _⊝_
data OutList : Set where
  □ : OutList
  _⊝_ : OutList → String → OutList

var-to-nat : {Γ : Ctx} {A : Ty} → Var Γ A → ℕ
var-to-nat 𝑧𝑣 = Z
var-to-nat (𝑠𝑣 v) = S (var-to-nat v)

print-var : {Γ : Ctx} {A : Ty} → Var Γ A → String
print-var v = showNat (var-to-nat v)

print-tm : {Γ : Ctx} {A : Ty} → Tm Γ A → String
print-app : {Γ : Ctx} {A : Ty} → Tm Γ A → String
print-lam : {Γ : Ctx} {A : Ty} → Tm Γ A → String

print-tm (V v) = print-var v
print-tm (Lam t) = parens ("λ" ++ print-lam t)
print-tm (App t s) = parens (print-app t ++ " " ++ print-tm s)

print-app (App t s) = print-app t ++ " " ++ print-tm s
{-# CATCHALL #-}
print-app t = print-tm t

print-lam (Lam t) = "λ" ++ print-lam t
{-# CATCHALL #-}
print-lam t = ". " ++ print-tm t

print-rule-∂₁ : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Rule t s → String
print-rule-∂₁ (β t s) = "⟪ λ. " ++ print-tm t ++ " " ++ print-tm s ++ "⟫"
print-rule-∂₁ (η t) = "⟪ " ++ print-tm t ++ " ⟫"

print-rule-∂₂ : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Rule t s → String
print-rule-∂₂ {Γ} (β t s) = "⟪ λ. " ++ print-tm (t [ idTms Γ ⊕ s ]) ++ "⟫"
print-rule-∂₂ {Γ} {A} (η t) = "⟪ λ. " ++ print-tm (W₁Tm A t) ++ " 0 ⟫"

print-env-∂₁ : {Γ : Ctx} {A : Ty} (env : Occurrence Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Rule t s → String
print-env-∂₁-app : {Γ : Ctx} {A : Ty} (env : Occurrence Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Rule t s → String
print-env-∂₁-lam : {Γ : Ctx} {A : Ty} (env : Occurrence Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Rule t s → String

print-env-∂₁ 𝑂 𝑅 = print-rule-∂₁ 𝑅
print-env-∂₁ (𝐿 env) 𝑅 = parens ("λ" ++ print-env-∂₁-lam env 𝑅)
print-env-∂₁ (𝐴₁ env s) 𝑅 = parens (print-env-∂₁-app env 𝑅 ++ " " ++ print-tm s)
print-env-∂₁ (𝐴₂ t env) 𝑅 = parens (print-app t ++ " " ++ print-env-∂₁ env 𝑅)

print-env-∂₁-app (𝐴₁ env s) 𝑅 = print-env-∂₁-app env 𝑅 ++ " " ++ print-tm s
print-env-∂₁-app (𝐴₂ t env) 𝑅 = print-app t ++ " " ++ print-env-∂₁ env 𝑅
{-# CATCHALL #-}
print-env-∂₁-app env 𝑅 = print-env-∂₁ env 𝑅

print-env-∂₁-lam (𝐿 env) 𝑅 = "λ" ++ print-env-∂₁-lam env 𝑅
{-# CATCHALL #-}
print-env-∂₁-lam env 𝑅 = ". " ++ print-env-∂₁ env 𝑅

print-env-∂₂ : {Γ : Ctx} {A : Ty} (env : Occurrence Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Rule t s → String
print-env-∂₂-app : {Γ : Ctx} {A : Ty} (env : Occurrence Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Rule t s → String
print-env-∂₂-lam : {Γ : Ctx} {A : Ty} (env : Occurrence Γ A) {t s : Tm (O-Γ env) (O-A env)} →
  Rule t s → String

print-env-∂₂ 𝑂 𝑅 = print-rule-∂₂ 𝑅
print-env-∂₂ (𝐿 env) 𝑅 = parens ("λ" ++ print-env-∂₂-lam env 𝑅)
print-env-∂₂ (𝐴₁ env s) 𝑅 = parens (print-env-∂₂-app env 𝑅 ++ " " ++ print-tm s)
print-env-∂₂ (𝐴₂ t env) 𝑅 = parens (print-app t ++ " " ++ print-env-∂₂ env 𝑅)

print-env-∂₂-app (𝐴₁ env s) 𝑅 = print-env-∂₂-app env 𝑅 ++ " " ++ print-tm s
print-env-∂₂-app (𝐴₂ t env) 𝑅 = print-app t ++ " " ++ print-env-∂₂ env 𝑅
{-# CATCHALL #-}
print-env-∂₂-app env 𝑅 = print-env-∂₂ env 𝑅

print-env-∂₂-lam (𝐿 env) 𝑅 = "λ" ++ print-env-∂₂-lam env 𝑅
{-# CATCHALL #-}
print-env-∂₂-lam env 𝑅 = ". " ++ print-env-∂₂ env 𝑅

print-boundary : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Step t s → String
print-boundary {t = t} ⟨ env ⊚ 𝑅 ⟩ = print-env-∂₁ env 𝑅
print-boundary {s = s} ⟨ env ⊚ 𝑅 ⟩⁻¹ = print-env-∂₂ env 𝑅

print-rule : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Rule t s → String
print-rule (β t s) = "    β"
print-rule (η t) = "    η"

print-step : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Step t s → String
print-step ⟨ env ⊚ 𝑅 ⟩ = print-rule 𝑅
print-step ⟨ env ⊚ 𝑅 ⟩⁻¹ = print-rule 𝑅 ++ " ⁻¹"

print-steps-helper : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Steps t s → OutList
print-steps-helper {s = s} [] = □
print-steps-helper (𝒮s ∷ 𝒮) = print-steps-helper 𝒮s ⊝ print-boundary 𝒮 ⊝ print-step 𝒮

print-steps : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Steps t s → OutList
print-steps {s = s} 𝒮s = print-steps-helper 𝒮s ⊝ print-tm s

format-out : OutList → String
format-out □ = ""
format-out (□ ⊝ s) = s
format-out (L ⊝ s ⊝ t) = format-out (L ⊝ s) ++ "\n" ++ t

format-steps : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Steps t s → String
format-steps 𝒮s = format-out (print-steps 𝒮s)
