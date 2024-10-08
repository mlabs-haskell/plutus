---
title: Nat
layout: page
---
```
module Declarative.Examples.StdLib.Nat where
```

```
open import Utils using (Kind;*)
open import Type using (Ctx⋆;_⊢⋆_;Z;S)
open Ctx⋆
open _⊢⋆_
open import Type.Equality using (_≡β_)
open _≡β_
import Type.RenamingSubstitution as ⋆
open import Declarative using (Ctx;_⊢_;_∋_)
open _⊢_
open _∋_
open import Declarative.Examples.StdLib.Function
```

```
G : ∀{Φ} → Φ ,⋆  * ⊢⋆ *
G = Π (` Z ⇒ (` (S Z) ⇒ ` Z) ⇒ ` Z)

M : ∀{Φ} → Φ ⊢⋆ *
M = μ0 · ƛ G

N : ∀{Φ} → Φ ⊢⋆ *
N  =  G ⋆.[ M ]

Zero : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
Zero = Λ (ƛ (ƛ (` (S (Z )))))

-- succ = λ n : N . Λ R . λ x : R . λ y : M → R . y (in n)
-- : N → N

Succ : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ
  (` Z · (wrap0 (ƛ G) (conv (sym≡β (β≡β _ _)) (` (S (S (T Z))))))))))

--FoldNat : ∀{Φ}{Γ : Ctx Φ} → {!!}
--FoldNat = {!!}
```
