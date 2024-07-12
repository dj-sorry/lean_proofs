{-# OPTIONS --without-K #-}

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Rational using (_+_ ; _*_ ; _<_ ; _>_ ; _/_)
open import Data.Rational.Unnormalised using (ℚᵘ)
open import Data.List using (List; length; filter)

-- Define the types for variables, contexts, and worlds
postulate
  Var : Set
  Context : Set
  World : Set

-- Define the predicate type
postulate Pred : Set

-- Define the interpretation of predicates in a given context and world
postulate interp : Pred → Context → World → Set

-- Define the existential quantifier
exists-quant : Pred → Pred → Context → World → Set
exists-quant p q c w = Σ Var (λ x → interp p c w × interp q c w)

-- Define the definite description
definite-desc : Pred → Pred → Context → World → Set
definite-desc p q c w = ∀ c' w' → interp p c' w' → interp q c' w'

-- Example proof: If there exists a variable assignment that satisfies both p and q, then the existential quantifier holds
example-exists-quant : {p q : Pred} {c : Context} {w : World} → Σ Var (λ x → interp p c w × interp q c w) → exists-quant p q c w
example-exists-quant {p} {q} {c} {w} x = x

-- Example proof: If for all contexts and worlds, if p is true then q is true, then the definite description holds
example-definite-desc : {p q : Pred} {c : Context} {w : World} → (∀ (c' : Context) (w' : World) → interp p c' w' → interp q c' w') → definite-desc p q c w
example-definite-desc {p} {q} {c} {w} h = h

-- Define the universal quantifier
every-quant : Pred → Pred → Context → World → Set
every-quant p q c w = ∀ (x : Var) → interp p c w → interp q c w

-- Define the majority quantifier
most-quant : Pred → Pred → Context → World → Set
most-quant p q c w =
  let p-count = Σ (List Var) (λ xs → Σ (List (Σ Var (λ x → interp p c w))) (λ ps → length ps > 0))
      pq-count = Σ (List Var) (λ xs → Σ (List (Σ Var (λ x → interp p c w × interp q c w))) (λ pqs → length pqs > (length xs / 2)))
  in p-count × pq-count

-- Example proof for EVERYX: If for all variable assignments, p implies q, then every-quant holds
example-every-quant : {p q : Pred} {c : Context} {w : World} → (∀ (x : Var) → interp p c w → interp q c w) → every-quant p q c w
example-every-quant {p} {q} {c} {w} h = h

-- Example proof for MOSTX: If for most variable assignments, p implies p & q in more than 50% of the cases, then most-quant holds
example-most-quant : {p q : Pred} {c : Context} {w : World} →
  (Σ (List Var) (λ xs → 
    (length (filter (λ x → interp p c w) xs) > 0) × 
    (length (filter (λ x → interp p c w × interp q c w) xs) > (length xs / 2)))) 
  → most-quant p q c w
example-most-quant {p} {q} {c} {w} (xs , (p-proof , pq-proof)) = 
  ((xs , (filter (λ x → interp p c w) xs , p-proof)) , 
   (xs , (filter (λ x → interp p c w × interp q c w) xs , pq-proof)))
