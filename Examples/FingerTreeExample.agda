{-# OPTIONS --sized-types #-}

module Examples.FingerTreeExample where

open import Data.FingerTree
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)

consExample : FingerTree ℕ
consExample = 1 ◁ 2 ◁ 3 ◁ 4 ◁ 5 ◁ 6 ◁ Empty
-- normalized: Deep (Two 1 2) (Single (Node3 3 4 5)) (One 6)

snocExample : FingerTree ℕ
snocExample = Empty ▷ 6 ▷ 7 ▷ 8
-- normalized: Deep (One 6) Empty (Two 7 8)

consSnocExample : FingerTree ℕ
consSnocExample = 0 ◁ consExample ▷ 6 ▷ 7
-- normalized: Deep (Two 0 1) (Single (Node3 2 3 4)) (Three 5 6 7)

headLExample : Maybe ℕ
headLExample = headL (0 ◁ 1 ◁ 2 ◁ Empty)
-- normalized: just 0

tailLExample : Maybe (FingerTree ℕ)
tailLExample = tailL (Empty ▷ 2 ▷ 1 ▷ 0)
-- normalized: just (Deep (One 1) Empty (One 0))

joinExample : FingerTree ℕ
joinExample = (1 ◁ 2 ◁ 3 ◁ Empty) ⋈ (4 ◁ 5 ◁ Empty)
-- normalized: Deep (Two 1 2) (Single (Node2 3 4)) (One 5)
