---
title: Type.BetaNBE.RenamingSubstitution
layout: page
---
```
module Type.BetaNBE.RenamingSubstitution where


open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;cong;cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_)

open import Utils using (*;♯;_⇒_)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S)
open _⊢⋆_
open import Type.Equality using (_≡β_;≡2β)
open _≡β_
open import Type.RenamingSubstitution
      using (Ren;ren;ext;ren-comp;sub;sub-id;sub-comp;sub-cong;exts;sub-ren;weaken;sub-∅)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;embNf;weakenNf;ren-embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNormal.Equality using (renNf-comp)
open import Type.BetaNBE using (reify;reflect;Env;eval;nf;renVal;idEnv;_,,⋆_;fresh;exte)
open import Type.BetaNBE.Soundness using (soundness)
open import Type.BetaNBE.Completeness
   using (EnvCR;CR;fund;ren-reify;idext;idCR;reifyCR;renCR;transCR;reflectCR;renVal-eval;renVal-reflect;symCR;ren-eval;sub-eval;completeness)
open import Type.BetaNBE.Stability using (stability)
```


Renaming is defined in the file Type.BetaNormal as it used in the
NBE algorithm.

reify ∘ reflect preserves the neutral term

```
reify-reflect : ∀{K Φ}(n : Φ ⊢Ne⋆ K) → reify (reflect n) ≡ ne n
reify-reflect {*}     n = refl
reify-reflect {♯}     n = refl
reify-reflect {K ⇒ J} n = refl
```

eval is closed under propositional equality for terms

```
evalCRSubst : ∀{Φ Ψ K}{η η' : Env Φ Ψ}
  → EnvCR η η'
  → {t t' : Φ ⊢⋆ K}
  → t ≡ t'
  → CR K (eval t η) (eval t' η')
evalCRSubst p {t = t} q = fund p (≡2β q)
```

```
ren-nf : ∀{ϕ ψ K}(σ : Ren ϕ ψ)(A : ϕ ⊢⋆ K) →
  renNf σ (nf A) ≡ nf (ren σ A)
ren-nf σ A = trans
  (ren-reify (idext idCR A) σ)
  (reifyCR
    (transCR
      (renVal-eval A idCR σ)
      (transCR
        (idext (renVal-reflect σ ∘ `) A)
        (symCR (ren-eval A idCR σ))  )))
```

```
ren-nf-μ : ∀ {Φ Ψ}{K}
  → (ρ⋆ : Ren Φ Ψ)
  → (A  : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
  → (B  : Φ ⊢Nf⋆ K)
  → renNf ρ⋆
    (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
    ≡
    nf
    (embNf (renNf ρ⋆ A) · ƛ (μ (embNf (weakenNf (renNf ρ⋆ A))) (` Z)) ·
     embNf (renNf ρ⋆ B))
ren-nf-μ ρ⋆ A B = trans
  (ren-nf ρ⋆ (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  (trans
    (cong₂
      (λ X Y → nf (X · ƛ (μ (ren (ext ρ⋆) (embNf (weakenNf A))) (` Z)) · Y))
      (sym (ren-embNf ρ⋆ A))
      (sym (ren-embNf ρ⋆ B)))
    (trans
      (cong
        (λ X → nf (embNf (renNf ρ⋆ A) · ƛ (μ (ren (ext ρ⋆) X) (` Z)) · embNf (renNf ρ⋆ B)))
        (ren-embNf S A))
      (cong
        (λ X → nf (embNf (renNf ρ⋆ A) · ƛ (μ X (` Z)) · embNf (renNf ρ⋆ B)))
        (trans
          (sym (ren-comp (embNf A)))
          (trans (sym (ren-embNf (S ∘ ρ⋆) A)) (cong embNf (renNf-comp A)))))))
```

```
SubNf : Ctx⋆ → Ctx⋆ → Set
SubNf φ Ψ = ∀ {J} → φ ∋⋆ J → Ψ ⊢Nf⋆ J
```

Substitution for normal forms:
1. embed back into syntax;
2. perform substitution;
3. renormalize.

```
subNf : ∀ {Φ Ψ}
  → SubNf Φ Ψ
    -------------------------
  → (∀ {J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J)
subNf ρ n = nf (sub (embNf ∘ ρ) (embNf n))
```

First monad law for subNf

```
subNf-id : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → subNf (ne ∘ `) n ≡ n
subNf-id n = trans
  (reifyCR (fund idCR (≡2β (sub-id (embNf n)))))
  (stability n)
```

This version of the first monad law might be η compatible as it doesn't rely
on sub-id

```
subNf-id' : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → subNf (nf ∘ `) n ≡ n
subNf-id' n = trans
  (reifyCR
    (transCR
      (sub-eval (embNf n) idCR (embNf ∘ nf ∘ `))
      (idext
        (λ α → fund idCR (≡2β (cong embNf (stability (ne (` α))))))
        (embNf n))))
  (stability n)
```

Second monad law for subNf
This is often holds definitionally for substitution (e.g. sub) but not here.

```
subNf-∋ : ∀ {Φ Ψ J}
  → (ρ : SubNf Φ Ψ)
  → (α : Φ ∋⋆ J)
  → subNf ρ (ne (` α)) ≡ ρ α
subNf-∋ ρ α = stability (ρ α)
```



Two lemmas that aim to remove a superfluous additional normalisation
via stability

```
subNf-nf : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
  → ∀ {J}
  → (t : Φ ⊢⋆ J)
    -------------------------------------------
  → nf (sub (embNf ∘ σ) t) ≡ subNf σ (nf t)
subNf-nf σ t = trans
  (reifyCR (sub-eval t idCR (embNf ∘ σ)))
  (trans
    (sym
      (reifyCR (fund (λ x → idext idCR (embNf (σ x))) (sym≡β (soundness t)))))
    (sym (reifyCR (sub-eval (embNf (nf t)) idCR (embNf ∘ σ)))))
```

Third Monad Law for subNf

```
subNf-comp : ∀{Φ Ψ Θ}
  (g : SubNf Φ Ψ)
  (f : SubNf Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    -----------------------------------------------
  → subNf (subNf f ∘ g) A ≡ subNf f (subNf g A)
subNf-comp g f A = trans
  (trans
    (trans
      (reifyCR
        (sub-eval
          (embNf A)
          idCR
          (embNf ∘ nf ∘ sub (embNf ∘ f) ∘ embNf ∘ g)))
      (trans (reifyCR
               (idext
                 (λ x → fund
                   idCR
                   (sym≡β (soundness (sub (embNf ∘ f) (embNf (g x))))))
                 (embNf A)))
             (sym
               (reifyCR
                 (sub-eval
                   (embNf A)
                   idCR
                   (sub (embNf ∘ f) ∘ embNf ∘ g))))))
    (completeness (≡2β (sub-comp (embNf A)))))
  (subNf-nf f (sub (embNf ∘ g) (embNf A)))
```

extending a normal substitution

```
extsNf : ∀ {Φ Ψ}
  → SubNf Φ Ψ
    -------------------------------
  → ∀ {K} → SubNf (Φ ,⋆ K) (Ψ ,⋆ K)
extsNf σ Z      =  ne (` Z)
extsNf σ (S α)  =  weakenNf (σ α)
```

cons for normal substitutions

```
subNf-cons : ∀{Φ Ψ}
  → (∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → ∀{J}(A : Ψ ⊢Nf⋆ J)
  → (∀{K} → Φ ,⋆ J ∋⋆ K → Ψ ⊢Nf⋆ K)
subNf-cons σ A Z     = A
subNf-cons σ A (S x) = σ x
```

Substitution of one variable

```
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = subNf (subNf-cons (ne ∘ `) B) A
```

Congruence lemma for sub
```
subNf-cong : ∀ {Φ Ψ}
  → {f g : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢Nf⋆ K)
    -------------------------------
  → subNf f A ≡ subNf g A
subNf-cong p A =
 reifyCR (fund idCR (≡2β (sub-cong (cong embNf ∘ p ) (embNf A))))
```

```
subNf-cong' : ∀ {Φ Ψ}
  → (f : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → ∀{K}{A A' : Φ ⊢Nf⋆ K}
  → A ≡ A'
    -------------------------------
  → subNf f A ≡ subNf f A'
subNf-cong' f p = cong (subNf f) p
```

Pushing renaming through normal substitution

```
renNf-subNf : ∀{Φ Ψ Θ}
  → (g : SubNf Φ Ψ)
  → (f : Ren Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
   -----------------------------------------------------
  → subNf (renNf f ∘ g) A ≡ renNf f (subNf g A)
renNf-subNf g f A = trans
  (reifyCR
    (transCR
      (transCR
        (sub-eval (embNf A) idCR (embNf ∘ renNf f ∘ g))
        (transCR
          (idext
            (λ α → transCR
              (evalCRSubst idCR (ren-embNf f (g α)))
              (transCR
                (ren-eval (embNf (g α)) idCR f)
                (idext (symCR ∘ renVal-reflect f ∘ `) (embNf (g α)))))
            (embNf A))
          (symCR (sub-eval (embNf A) (renCR f ∘ idCR) (embNf ∘ g)))))
      (symCR (renVal-eval (sub (embNf ∘ g) (embNf A)) idCR f))))
  (sym (ren-reify (idext idCR (sub (embNf ∘ g) (embNf A))) f))
```

Pushing a substitution through a renaming

```
subNf-renNf : ∀{Φ Ψ Θ}
  → (g : Ren Φ Ψ)
  → (f : SubNf Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    --------------------------------------
  → subNf (f ∘ g) A ≡ subNf f (renNf g A)
subNf-renNf g f A = reifyCR
  (transCR
    (sub-eval (embNf A) idCR (embNf ∘ f ∘ g))
    (transCR
      (transCR
        (symCR (ren-eval (embNf A) (λ α → idext idCR (embNf (f α))) g))
        (symCR
          (evalCRSubst (λ α → idext idCR (embNf (f α))) (ren-embNf g A))))
      (symCR (sub-eval (embNf (renNf g A)) idCR (embNf ∘ f)))))
```

Pushing renaming through a one variable normal substitution

```
ren[]Nf : ∀ {Φ Θ J K}
        → (ρ : Ren Φ Θ)
        → (t : Φ ,⋆ K ⊢Nf⋆ J)
        → (u : Φ ⊢Nf⋆ K )
          --------------------------------------------------------------
        → renNf ρ (t [ u ]Nf) ≡ (renNf (ext ρ) t [ renNf ρ u ]Nf)
ren[]Nf ρ t u = trans
  (sym (renNf-subNf (subNf-cons (ne ∘ `) u) ρ t))
  (trans
    (subNf-cong
      {f = renNf ρ ∘ subNf-cons (ne ∘ `) u}
      {g = subNf-cons (ne ∘ `) (renNf ρ u) ∘ ext ρ}
      (λ { Z → refl ; (S α) → refl})
      t)
    (subNf-renNf (ext ρ)(subNf-cons (ne ∘ `) (renNf ρ u)) t))
```

Pushing a normal substitution through a one place normal substitution

```
sub[]Nf : ∀{Φ Ψ K J}
  → (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (A : Φ ⊢Nf⋆ K)
  → (B : Φ ,⋆ K ⊢Nf⋆ J)
    --------------------------------------------------------------
  → subNf ρ (B [ A ]Nf) ≡ (subNf (extsNf ρ) B [ subNf ρ A ]Nf)
sub[]Nf ρ A B = trans
  (sym (subNf-comp (subNf-cons (ne ∘ `) A) ρ B))
  (trans
    (subNf-cong
      {f = subNf ρ ∘ subNf-cons (ne ∘ `) A}
      {g = subNf (subNf-cons (ne ∘ `) (subNf ρ A)) ∘ extsNf ρ}
      (λ { Z     → sym (subNf-∋ (subNf-cons (ne ∘ `) (subNf ρ A)) Z)
         ; (S α) → trans
              (trans (subNf-∋ ρ α) (sym (subNf-id (ρ α))))
              (subNf-renNf
                S
                (subNf-cons (ne ∘ `) (subNf ρ A))
                (ρ α))})
      B)
    (subNf-comp  (extsNf ρ) (subNf-cons (ne ∘ `) (subNf ρ A)) B))
```

Extending a normal environment and then embedding is the same as
embedding and then extending.

```
subNf-lemma : ∀{Φ Ψ K J}
  (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (t : Φ ,⋆ K ⊢⋆ J)
  → sub (exts (embNf ∘ ρ)) t ≡ sub (embNf ∘ extsNf ρ) t
subNf-lemma ρ t =
  sub-cong (λ { Z → refl ; (S x) → sym (ren-embNf S (ρ x))}) t
```

Repair a mismatch between two different ways of extending an environment

```
subNf-lemma' : ∀{Φ K J}
  → (B : Φ ,⋆ K ⊢⋆ J)
  → nf B ≡ reify (eval B ((renVal S ∘ idEnv _) ,,⋆ fresh))
subNf-lemma' B = reifyCR
  (idext (λ { Z     → reflectCR refl
            ; (S x) → symCR (renVal-reflect S (` x))}) B)
```

combining the above lemmas

note: there are several mismatches here, one due to two different ways
of extending a normal substitution and another due to two different
ways of extending an environment

```
sub[]Nf' : ∀{Φ Ψ K J}
  → (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (A : Φ ⊢Nf⋆ K)
  → (B : Φ ,⋆ K ⊢Nf⋆ J)
  → subNf ρ (B [ A ]Nf)
    ≡
    ((reify (eval (sub (exts (embNf ∘ ρ)) (embNf B))
                 ((renVal S ∘ idEnv _) ,,⋆ fresh)))
    [ subNf ρ A ]Nf)
sub[]Nf' ρ A B =
  trans (sub[]Nf ρ A B)
  (subNf-cong' (subNf-cons (ne ∘ `) (subNf ρ A))
     {A = subNf (extsNf ρ) B}
     {A' =
      reify
      (eval (sub (exts (embNf ∘ ρ)) (embNf B))
       ((renVal S ∘ idEnv _) ,,⋆ fresh))}
     (trans (sym (completeness (≡2β (subNf-lemma ρ (embNf B)))))
              (subNf-lemma'  (sub (exts (embNf ∘ ρ)) (embNf B)))))
```

```
weakenNf-renNf : ∀ {Φ Ψ}
  → (ρ⋆ : Ren Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf (renNf ρ⋆ A) ≡ renNf (ext ρ⋆ {K = K}) (weakenNf A)
weakenNf-renNf ρ⋆ A = trans (sym (renNf-comp _)) (renNf-comp _)

weakenNf-subNf : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf (subNf σ⋆ A) ≡ subNf (extsNf σ⋆ {K = K}) (weakenNf A)
weakenNf-subNf σ⋆ A = trans
  (sym (renNf-subNf σ⋆ S A))
  (subNf-renNf S (extsNf σ⋆) A)

weakenNf[] : ∀ {Φ K}(B : Φ ⊢Nf⋆ K)
        → (A : Φ ⊢Nf⋆ *)
        → A ≡ (weakenNf A [ B ]Nf)
weakenNf[] B A = trans
  (trans (sym (stability A))
         (evalCRSubst idCR (sym (sub-id (embNf A)))))
  (subNf-renNf S (subNf-cons (ne ∘ `) B) A)



sub-nf-Π : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → ∀{K}
  → (B : Φ ,⋆ K ⊢Nf⋆ *)
  → subNf (extsNf σ⋆) B
    ≡
    eval (sub (exts (embNf ∘ σ⋆)) (embNf B)) (exte (idEnv Ψ))
sub-nf-Π σ⋆ B = trans
  (evalCRSubst idCR (sym (subNf-lemma σ⋆ (embNf B))))
  (subNf-lemma' (sub (exts (embNf ∘ σ⋆)) (embNf B)))

sub-nf-μ : ∀ {Φ Ψ}{K}
  → (σ⋆ : SubNf Φ Ψ)
  → (A  : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
  → (B  : Φ ⊢Nf⋆ K)
  → subNf σ⋆ (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
    ≡
    nf
    (embNf (subNf σ⋆ A) ·
     ƛ (μ (embNf (weakenNf (subNf σ⋆ A))) (` Z))
     · embNf (subNf σ⋆ B))
sub-nf-μ σ⋆ A B = trans
  (sym (subNf-nf σ⋆ (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)))
  (completeness
    {s = sub (embNf ∘ σ⋆) (embNf A) · ƛ (μ (sub (exts (embNf ∘ σ⋆)) (embNf (weakenNf A))) (` Z)) · sub (embNf ∘ σ⋆) (embNf B)}
    {(embNf (subNf σ⋆ A) · ƛ (μ (embNf (weakenNf (subNf σ⋆ A))) (` Z)) · embNf (subNf σ⋆ B))}
    (·≡β
      (·≡β
        (soundness (sub (embNf ∘ σ⋆) (embNf A)))
        (ƛ≡β (μ≡β
          (trans≡β
            (trans≡β
              (≡2β (cong (sub (exts (embNf ∘ σ⋆))) (ren-embNf S A)))
              (trans≡β
                (≡2β (sym (sub-ren (embNf A))))
                (trans≡β
                  (soundness (sub (weaken ∘ embNf ∘ σ⋆) (embNf A)))
                  (≡2β
                    (cong embNf {nf (sub (weaken ∘ embNf ∘ σ⋆) (embNf A))}{subNf (renNf S ∘ σ⋆) A}
                    (cong nf (sub-cong (sym ∘ ren-embNf S ∘ σ⋆) (embNf A))))))))
            (≡2β (cong embNf (renNf-subNf σ⋆ S A))))
          (refl≡β (` Z)))))
      (soundness (sub (embNf ∘ σ⋆) (embNf B)))))
```

```
subNf-cons-[]Nf : ∀{Φ K Ψ'}{σ : SubNf Ψ' Φ}{A : Φ ⊢Nf⋆ K}(X : Ψ' ,⋆ K ⊢Nf⋆ *) →
  subNf (subNf-cons σ A) X
  ≡
  reify (eval (sub (exts (embNf ∘ σ)) (embNf X)) (exte (idEnv Φ))) [ A ]Nf
subNf-cons-[]Nf {σ = σ}{A} X = trans
  (trans (subNf-cong {f = subNf-cons σ A}{g = subNf (subNf-cons (ne ∘ `) A) ∘ extsNf σ} (λ {Z → sym (stability A) ; (S α) → trans (trans (sym (stability (σ α))) (cong nf (sym (sub-id (embNf (σ α)))))) (subNf-renNf S (subNf-cons (ne ∘ `) A) (σ α)) }) X)
         (subNf-comp (extsNf σ)
                       (subNf-cons (ne ∘ `) A)
                       X))
  (cong (_[ A ]Nf)
        (sub-nf-Π σ X))
```

```
-- A version of subNf that is definitionally the identity on the empty context
subNf∅ : ∀{Φ K} → ∅ ⊢Nf⋆ K → Φ ⊢Nf⋆ K
subNf∅ {∅} t = t
subNf∅ {Φ ,⋆ x} t = subNf (λ()) t

-- But this is equivalent to the normal subNf
subNf∅≡subNf : ∀{Φ K} → {A : ∅ ⊢Nf⋆ K} → subNf∅ {Φ} A ≡ subNf (λ()) A
subNf∅≡subNf {∅} {_} {A} = begin
             A
            ≡⟨ sym (stability A) ⟩
             nf (embNf A)
           ≡⟨ cong nf (sym (sub-∅ (embNf A)  (embNf ∘  λ()))) ⟩
             nf (sub (embNf ∘ λ()) (embNf A))
           ≡⟨ refl ⟩
             subNf (λ ()) A
           ∎
subNf∅≡subNf {Φ ,⋆ x} = refl

subNf∅-renNf : ∀{Φ Ψ K} (ρ : Ren Φ Ψ) (A : ∅ ⊢Nf⋆ K) → renNf ρ (subNf∅ A) ≡ subNf∅ A
subNf∅-renNf ρ A = begin
            renNf ρ (subNf∅ A)
          ≡⟨ cong (renNf ρ) subNf∅≡subNf ⟩
             renNf ρ (subNf (λ ()) A)
         ≡⟨ sym (renNf-subNf (λ()) ρ A)  ⟩
            subNf (renNf ρ ∘ (λ ())) A
          ≡⟨ sym (subNf-cong {f = λ()} {renNf ρ ∘ λ ()} (λ ()) A) ⟩
            subNf (λ ()) A
          ≡⟨ sym subNf∅≡subNf ⟩
           subNf∅ A
          ∎

subNf∅-subNf : ∀{Φ Ψ K} → (σ : SubNf Φ Ψ) → (A : ∅ ⊢Nf⋆ K) → subNf σ (subNf∅ A) ≡ subNf∅ A
subNf∅-subNf σ A = begin
             subNf σ (subNf∅ A)
          ≡⟨ cong (subNf σ) subNf∅≡subNf ⟩
             subNf σ (subNf (λ ()) A)
          ≡⟨ sym (subNf-comp (λ()) σ A) ⟩
            subNf (subNf σ ∘ (λ ())) A
          ≡⟨ subNf-cong {f = subNf σ ∘ (λ ())} {λ ()} (λ ()) A ⟩
            subNf (λ ()) A
          ≡⟨ sym subNf∅≡subNf ⟩
           subNf∅ A
          ∎
```
