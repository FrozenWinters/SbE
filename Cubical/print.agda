{-# OPTIONS --cubical #-}

module print where

open import lists
open import syn
open import trace

open import Data.String

infixl 20 _∷L_
data OutList : Type where
  []L : OutList
  _∷L_ : OutList → String → OutList

print-var : {Γ : Ctx} {A : Ty} → Var Γ A → String
print-var 𝑧𝑣 = "𝑧𝑣"
print-var (𝑠𝑣 v) = "(𝑠𝑣 " ++ print-var v ++ ")"

print-tm : {Γ : Ctx} {A : Ty} → Tm Γ A → String
print-tm (V v) = "(V " ++ print-var v ++ ")"
print-tm (Lam t) = "(Lam " ++ print-tm t ++ ")"
print-tm (App t s) = "(App " ++ print-tm t ++ " " ++ print-tm s ++ ")"

print-rule : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Rule t s → String
print-rule (β t s) = "β " ++ print-tm t ++ " " ++ print-tm s
print-rule (η t) = "η " ++ print-tm t

print-trace : {Γ : Ctx} {A : Ty} {t s : Tm Γ A} → Steps t s → OutList
print-trace {t = t} [] = []L ∷L print-tm t
print-trace {s = s} (𝒮s ∷ ⟨ env ⊚ 𝑅 ⟩) =
  print-trace 𝒮s ∷L print-rule 𝑅 ∷L print-tm s
print-trace {s = s} (𝒮s ∷ ⟨ env ⊚ 𝑅 ⟩⁻¹) =
  print-trace 𝒮s ∷L (print-rule 𝑅 ++ " ⁻¹") ∷L print-tm s
print-trace (𝒮s ∷ sub⟨ a ⟩) = print-trace 𝒮s
