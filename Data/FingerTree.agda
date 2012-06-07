------------------------------------------------------------------------
-- Finger trees for Agda
------------------------------------------------------------------------

-- Finger trees are an efficient general-purpose data structure.

-- This module implements non-dependent finger trees and is very
-- similar to the Haskell version described by Hinze and Paterson
-- in their paper "Finger Trees: A Simple General-purpose Data
-- Structure" (2006).

-- Finger trees support many different operations. The most important
-- ones are:
--  • _◁_; _▷_ (a.k.a cons and snoc)
--  • headL; tailL; headR; tailR (a.k.a head, tail, init and last)
--  • viewL; viewR (allow list-like views)
--  • toList; toTree (conversion from - and to lists)
--  • isEmpty (a.k.a null)
--  • _⋈_ (a.k.a _++_)

{-# OPTIONS --sized-types #-}

module Data.FingerTree where

open import Class.Reduce
open import Level using (Level)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _⁺++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Size

------------------------------------------------------------------------
-- Finger tree =
--   Digit (of Nodes) + Finger Tree (of Nodes) + Digit (of Nodes)

data Node {a : Level} (A : Set a) : Set a where
  Node2 : A → A → Node A
  Node3 : A → A → A → Node A

data Digit {a : Level} (A : Set a) : Set a where
  One   : A → Digit A
  Two   : A → A → Digit A
  Three : A → A → A → Digit A
  Four  : A → A → A → A → Digit A

data FingerTree {a : Level} (A : Set a) : {size : Size} → Set a where
  Empty  : {i : Size} → FingerTree A {↑ i}
  Single : {i : Size} → A → FingerTree A {↑ i}
  Deep   : ∀ {i : Size} → Digit A → FingerTree (Node A) {i} → Digit A →
           FingerTree A {↑ i}

------------------------------------------------------------------------
-- cons and snoc

infixr 5 _◁_
_◁_ : ∀ {i a} {A : Set a} → A → FingerTree A {i} → FingerTree A {↑ i}
a ◁ Empty                     = Single a
a ◁ Single b                  = Deep (One   a) Empty (One b)
a ◁ Deep (One   b) m sf       = Deep (Two   a b) m sf
a ◁ Deep (Two   b c) m sf     = Deep (Three a b c) m sf
a ◁ Deep (Three b c d) m sf   = Deep (Four  a b c d) m sf
a ◁ Deep (Four  b c d e) m sf = Deep (Two   a b) (Node3 c d e ◁ m) sf

infixl 5 _▷_
_▷_ : ∀ {i a} {A : Set a} → FingerTree A {i} → A → FingerTree A {↑ i}
Empty                     ▷ a = Single a
Single b                  ▷ a = Deep (One b) Empty (One a)
Deep pr m (One   b)       ▷ a = Deep pr m (Two   b a)
Deep pr m (Two   c b)     ▷ a = Deep pr m (Three c b a)
Deep pr m (Three d c b)   ▷ a = Deep pr m (Four  d c b a)
Deep pr m (Four  e d c b) ▷ a = Deep pr (m ▷ Node3 e d c) (Two b a)

------------------------------------------------------------------------
-- Instances of the Reduce type class

reducerNode : ∀ {a} {A : Set a} {B : Set a} → (A → B → B) → Node A → B → B
reducerNode _⤙_ (Node2 a b) z   = a ⤙ (b ⤙ z)
reducerNode _⤙_ (Node3 a b c) z = a ⤙ (b ⤙ (c ⤙ z))

reducelNode : ∀ {a} {A : Set a} {B : Set a} → (B → A → B) → B → Node A → B
reducelNode _⤚_ z (Node2 b a)   = (z ⤚ b) ⤚ a
reducelNode _⤚_ z (Node3 c b a) = ((z ⤚ c) ⤚ b) ⤚ a

reduceInstanceNode : {a : Level} → reduceClass Node
reduceInstanceNode {a} = record {
  reducer = reducerNode {a} ;
  reducel = reducelNode }

reducerDigit : ∀ {a} {A : Set a} {B : Set a} → (A → B → B) → Digit A → B → B
reducerDigit _⤙_ (One a)        z = a ⤙ z
reducerDigit _⤙_ (Two a b)      z = a ⤙ (b ⤙ z)
reducerDigit _⤙_ (Three a b c)  z = a ⤙ (b ⤙ (c ⤙ z))
reducerDigit _⤙_ (Four a b c d) z = a ⤙ (b ⤙ (c ⤙ (d ⤙ z)))

reducelDigit : ∀ {a} {A : Set a} {B : Set a} → (B → A → B) → B → Digit A → B
reducelDigit _⤚_ z (One a)        = z ⤚ a
reducelDigit _⤚_ z (Two b a)      = (z ⤚ b) ⤚ a
reducelDigit _⤚_ z (Three c b a)  = ((z ⤚ b) ⤚ c) ⤚ a
reducelDigit _⤚_ z (Four d b c a) = (((z ⤚ d) ⤚ c) ⤚ b) ⤚ a

reduceInstanceDigit : {a : Level} → reduceClass Digit
reduceInstanceDigit {a} = record {
  reducer = reducerDigit {a};
  reducel = reducelDigit }

reducerFingerTree : ∀ {a} {A : Set a} {B : Set a} → {i : Size} →
                    (A → B → B) → FingerTree A {i} → B → B
reducerFingerTree {a} {A} {B} {.(↑ i)} _⤙_ (Empty {i}) z = z
reducerFingerTree {a} {A} {B} {.(↑ i)} _⤙_ (Single {i} x) z = x ⤙ z
reducerFingerTree {a} {A} {B} {.(↑ i)} _⤙_ (Deep {i} pr m sf) z = pr ⤙′ (m ⤙″ (sf ⤙′ z))
  where _⤙′_ : Digit A → B → B
        _⤙′_  = reducerDigit _⤙_
        _⤙″_ : FingerTree (Node A) {i} → B → B
        _⤙″_ = reducerFingerTree (reducerNode _⤙_)

reducelFingerTree : ∀ {a} {A : Set a} {B : Set a} → {i : Size} →
                    (B → A → B) → B → FingerTree A {i} → B
reducelFingerTree {a} {A} {B} {.(↑ i)} _⤚_ z (Empty {i}) = z
reducelFingerTree {a} {A} {B} {.(↑ i)} _⤚_ z (Single {i} x) = z ⤚ x
reducelFingerTree {a} {A} {B} {.(↑ i)} _⤚_ z (Deep {i} pr m sf) = ((z ⤚′ pr) ⤚″ m ) ⤚′ sf
  where _⤚′_ : B → Digit A → B
        _⤚′_  = reducelDigit _⤚_
        _⤚″_ : B → FingerTree (Node A) {i} → B
        _⤚″_ = reducelFingerTree (reducelNode _⤚_)

reduceInstanceFingerTree : {a : Level} → reduceClass (λ A → FingerTree A)
reduceInstanceFingerTree {a} = record {
  reducer = reducerFingerTree {a};
  reducel = reducelFingerTree }

------------------------------------------------------------------------
-- Lifted cons and snoc

_◁′_ : ∀ {a} {F : Set a → Set a} {{r : reduceClass F}} {A : Set a} →
       F A → FingerTree A → FingerTree A
_◁′_ = reducer _◁_

_▷′_ : ∀ {a} {F : Set a → Set a} {{r : reduceClass F}} {A : Set a} →
       FingerTree A → F A → FingerTree A
_▷′_ = reducel _▷_

------------------------------------------------------------------------
-- A few helper functions

toTree : ∀ {a} {F : Set a → Set a} {{r : reduceClass F}} {A : Set a} →
         F A → FingerTree A
toTree s = s ◁′ Empty

head : ∀ {a} {A : Set a} → Digit A → A
head (One a) = a
head (Two a b) = a
head (Three a b c) = a
head (Four a b c d) = a

tail : ∀ {a} {A : Set a} → Digit A → Maybe (Digit A)
tail (One a) = nothing
tail (Two a b) = just (One b)
tail (Three a b c) = just (Two b c)
tail (Four a b c d) = just (Three b c d)

------------------------------------------------------------------------
-- The view, headL and tailL

data ViewL {a : Level} (A : Set a) : Set a where
  nilL : ViewL A
  consL : A → FingerTree A → ViewL A

mutual
  viewL : ∀ {a} {A : Set a} → FingerTree A → ViewL A
  viewL Empty = nilL
  viewL (Single x) = consL x Empty
  viewL (Deep pr m sf) = consL (head pr) (deepL (tail pr) m sf)

  deepL : ∀ {a} {A : Set a} → Maybe (Digit A) →
           FingerTree (Node A) → Digit A → FingerTree A
  deepL (just pr) m sf = Deep pr m sf
  deepL nothing m sf with viewL m
  ...                | nilL = toTree sf
  ...                | consL (Node2 a b)   m′ = Deep (Two a b) m′ sf
  ...                | consL (Node3 a b c) m′ = Deep (Three a b c) m′ sf

isEmpty : ∀ {a} {A : Set a} → FingerTree A → Bool
isEmpty x with viewL x
...       | nilL      = true
...       | consL _ _ = false

headL : ∀ {a} {A : Set a} → FingerTree A → Maybe A
headL x with viewL x
...     | nilL      = nothing
...     | consL a _ = just a

tailL : ∀ {a} {A : Set a} → FingerTree A → Maybe (FingerTree A)
tailL x with viewL x
...     | nilL      = nothing
...     | consL _ b = just b

------------------------------------------------------------------------
-- The corresponding views and head + tail on the right side

last : ∀ {a} {A : Set a} → Digit A → A
last (One a)        = a
last (Two a b)      = b
last (Three a b c)  = c
last (Four a b c d) = d

init : ∀ {a} {A : Set a} → Digit A → Maybe (Digit A)
init (One a)        = nothing
init (Two a b)      = just (One b)
init (Three a b c)  = just (Two a b)
init (Four a b c d) = just (Three a b c)

data ViewR {a : Level} (A : Set a) : Set a where
  nilR : ViewR A
  consR : FingerTree A → A → ViewR A

mutual
  viewR : ∀ {a} {A : Set a} → FingerTree A → ViewR A
  viewR Empty = nilR
  viewR (Single x) = consR Empty x
  viewR (Deep pr m sf) = consR (deepR pr m (init sf)) (last sf)

  deepR : ∀ {a} {A : Set a} → Digit A → FingerTree (Node A) →
          Maybe (Digit A) → FingerTree A
  deepR pr m (just sf) = Deep pr m sf
  deepR pr m nothing with viewR m
  ...                | nilR = toTree pr
  ...                | consR m′ (Node2 a b)   = Deep pr m′ (Two a b)
  ...                | consR m′ (Node3 a b c) = Deep pr m′ (Three a b c)

headR : ∀ {a} {A : Set a} → FingerTree A → Maybe A
headR x with viewR x
...     | nilR      = nothing
...     | consR _ a = just a

tailR : ∀ {a} {A : Set a} → FingerTree A → Maybe (FingerTree A)
tailR x with viewR x
...     | nilR      = nothing
...     | consR b _ = just b

------------------------------------------------------------------------
-- Helper functions for concatenation

data List⁺⁺ {a} (A : Set a) : Set a where
  [_,_] : (x : A) → (y : A) → List⁺⁺ A
  _∷_ : (x : A) (xs : List⁺⁺ A) → List⁺⁺ A

_⁺++⁺_ : ∀ {a} {A : Set a} → List⁺ A → List⁺ A → List⁺⁺ A
[ x ]    ⁺++⁺ [ y ]    = [ x , y ]
[ x ]    ⁺++⁺ (y ∷ ys) = x ∷ ([ y ] ⁺++⁺ ys)
(x ∷ xs) ⁺++⁺ ys       = x ∷ (xs ⁺++⁺ ys)

toList⁺ : ∀ {a} {A : Set a} → Digit A → List⁺ A
toList⁺ (One a)        = [ a ]
toList⁺ (Two a b)      = a ∷ [ b ]
toList⁺ (Three a b c)  = a ∷ b ∷ [ c ]
toList⁺ (Four a b c d) = a ∷ b ∷ c ∷ [ d ]

toList⁺⁺ : ∀ {a} {A : Set a} → Digit A → List A → Digit A → List⁺⁺ A
toList⁺⁺ sf ts pr = (toList⁺ sf ⁺++ ts) ⁺++⁺ toList⁺ pr

nodes : ∀ {a} {A : Set a} → List⁺⁺ A → List (Node A)
nodes [ a , b ]           = (Node2 a b) ∷ []
nodes (a ∷ [ b , c ])     = (Node3 a b c) ∷ []
nodes (a ∷ b ∷ [ c , d ]) = (Node2 a b) ∷ (Node2 c d) ∷ []
nodes (a ∷ b ∷ c ∷ xs)    = (Node3 a b c) ∷ (nodes xs)

app3 : ∀ {a} {A : Set a} → FingerTree A → List A → FingerTree A → FingerTree A
app3 Empty ts xs      = ts ◁′ xs
app3 xs ts Empty      = xs ▷′ ts
app3 (Single x) ts xs = x ◁ (ts ◁′ xs)
app3 xs ts (Single x) = (xs ▷′ ts) ▷ x
app3 (Deep pr₁ m₁ sf₁) ts (Deep pr₂ m₂ sf₂)
  = Deep pr₁ (app3 m₁ (nodes ((toList⁺⁺ sf₁ ts pr₂))) m₂) sf₂

------------------------------------------------------------------------
-- Concatenation itself

_⋈_ : ∀ {a} {A : Set a} → FingerTree A → FingerTree A → FingerTree A
xs ⋈ ys = app3 xs [] ys
