{-# OPTIONS --cubical #-}

module tests where

open import lists
open import syn
open import trace
open import norm
open import print

open import Cubical.Data.Nat renaming (zero to Z; suc to S)

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

sum = 𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 (Base 'A') 0 0

𝐼𝑑 : (A : Ty) → Tm ∅ (A ⇒ A)
𝐼𝑑 A = Lam (V 𝑧𝑣)

idA⇒A = 𝐼𝑑 (Base 'A' ⇒ Base 'A')

idA = 𝐼𝑑 (Base 'A')

test1 = print-trace (correctness idA⇒A)

test2 = print-trace (correctness (App idA⇒A idA))

test3 = print-trace (correctness (App (Plus {∅} {Base 'A'}) (𝐶𝑁𝑢𝑚 0)))

test4 =  print-trace (correctness (𝐶𝑁𝑢𝑚 {∅} {Base 'A'} 10))
