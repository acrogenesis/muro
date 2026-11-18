------------------------------------------------------------------------
-- A list of directed moves is a legal prefix of a protocol.
--
-- The protocol fragment is the finite one: end, send, recv, choose,
-- and branch. A move is a value sent or received, or a label that
-- selects an arm. The empty list is a prefix of every protocol,
-- including one this fragment does not step. A derivation is a
-- legal prefix. `accept` decides this fragment, and `accept-sound`
-- says a list it accepts has a derivation.
--
-- This is not a source syntax. None of these constructors is added
-- to Tm. Recursion, a named continuation, a dependent payload, an
-- evidence bound, an indexed bit, a case, and the numeric position
-- the C stepper assigns are not this theorem. The Elixir checker
-- decides those. The generated C program is not proved.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Prefix where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable.Core using () renaming (yes to yes′; no to no′)

open import Muro.Session using (
  Proto; Ty; Val; fits; end; send; recv; dsend; drecv; esend; erecv;
  isend; irecv; choose; branch; pcase; nat; bit; zero; b0; b1; ty≟;
  Decl; mkDecl; Spine; snil; con; dat)

------------------------------------------------------------------------
-- A directed move. `out` is send. `inn` is receive. `say` carries a
-- value of the payload type. `sel` carries the bit that selects an
-- arm: `b0` is the left arm and `b1` is the right arm.
------------------------------------------------------------------------

data Dir : Set where
  out : Dir
  inn : Dir

data Mv : Set where
  say : Dir → (A : Ty) → Val A → Mv
  sel : Dir → Val bit → Mv

------------------------------------------------------------------------
-- `Leg ms S` is a derivation that `ms` is a legal prefix of `S`.
-- The empty list stops at any protocol. Each other rule consumes
-- one move and continues on the protocol that move selects.
------------------------------------------------------------------------

data Leg : List Mv → Proto → Set where
  halt : ∀ {S} → Leg [] S

  go-send : ∀ {A v ms S} →
    fits v ≡ true → Leg ms S →
    Leg (say out A v ∷ ms) (send A S)

  go-recv : ∀ {A v ms S} →
    fits v ≡ true → Leg ms S →
    Leg (say inn A v ∷ ms) (recv A S)

  go-c0 : ∀ {ms S T} → Leg ms S → Leg (sel out b0 ∷ ms) (choose S T)
  go-c1 : ∀ {ms S T} → Leg ms T → Leg (sel out b1 ∷ ms) (choose S T)
  go-b0 : ∀ {ms S T} → Leg ms S → Leg (sel inn b0 ∷ ms) (branch S T)
  go-b1 : ∀ {ms S T} → Leg ms T → Leg (sel inn b1 ∷ ms) (branch S T)

------------------------------------------------------------------------
-- Two moves, and the same judgment read from the continuation.
------------------------------------------------------------------------

wire : Proto
wire = send nat (recv bit end)

two : Leg (say out nat zero ∷ say inn bit b0 ∷ []) wire
two = go-send refl (go-recv refl halt)

rest : Proto
rest = recv bit end

mid : Leg (say inn bit b1 ∷ []) rest
mid = go-recv refl halt

from-cont : Leg (say inn bit b1 ∷ []) (recv bit end)
from-cont = mid

-- The empty prefix is legal for a protocol this fragment does not step.
halt-dep : Leg [] (dsend "n" nat end)
halt-dep = halt

------------------------------------------------------------------------
-- Refusals. Each of these has no derivation.
------------------------------------------------------------------------

bad-dir : ¬ Leg (say inn nat zero ∷ []) (send nat end)
bad-dir ()

bad-end : ¬ Leg (say out nat zero ∷ []) end
bad-end ()

bad-pick : ¬ Leg (sel out b0 ∷ []) (send nat end)
bad-pick ()

emptyD : Decl
emptyD = mkDecl "Empty" nzero []

bad-ctor :
  ¬ Leg (say inn (dat emptyD []) (con {emptyD} {[]} "nope" snil) ∷ [])
        (recv (dat emptyD []) end)
bad-ctor (go-recv () _)

------------------------------------------------------------------------
-- Decision. A type the move does not carry, and every protocol
-- outside the five forms, is false. Completeness is not claimed.
------------------------------------------------------------------------

mutual
  accept : List Mv → Proto → Bool
  accept [] _ = true
  accept (say out A v ∷ ms) (send B S) with ty≟ A B
  ... | no′ _ = false
  ... | yes′ refl = fits v ∧ accept ms S
  accept (say inn A v ∷ ms) (recv B S) with ty≟ A B
  ... | no′ _ = false
  ... | yes′ refl = fits v ∧ accept ms S
  accept (sel out b ∷ ms) (choose S T) = arm b ms S T
  accept (sel inn b ∷ ms) (branch S T) = arm b ms S T
  accept _ _ = false

  -- The bit is split only after the protocol matches. A selector at
  -- any other protocol is false without knowing which bit it carries.
  arm : Val bit → List Mv → Proto → Proto → Bool
  arm b0 ms S _ = accept ms S
  arm b1 ms _ T = accept ms T

two-accepts : accept (say out nat zero ∷ say inn bit b0 ∷ []) wire ≡ true
two-accepts = refl

mid-accepts : accept (say inn bit b1 ∷ []) rest ≡ true
mid-accepts = refl

∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-true {true} {b} eq = refl , eq
∧-true {false} {_} ()

mutual
  accept-sound : ∀ ms S → accept ms S ≡ true → Leg ms S
  accept-sound [] _ _ = halt
  accept-sound (say out A v ∷ ms) S eq = say-out A v ms S eq
  accept-sound (say inn A v ∷ ms) S eq = say-inn A v ms S eq
  accept-sound (sel out b ∷ ms) S eq = sel-out b ms S eq
  accept-sound (sel inn b ∷ ms) S eq = sel-inn b ms S eq

  say-out : ∀ A v ms S →
    accept (say out A v ∷ ms) S ≡ true → Leg (say out A v ∷ ms) S
  say-out A v ms (send B S) eq with ty≟ A B
  ... | yes′ refl =
    go-send (proj₁ (∧-true eq)) (accept-sound ms S (proj₂ (∧-true eq)))
  ... | no′ _ = ⊥-from eq
    where
      ⊥-from : false ≡ true → Leg (say out A v ∷ ms) (send B S)
      ⊥-from ()
  say-out _ _ _ end ()
  say-out _ _ _ (recv _ _) ()
  say-out _ _ _ (dsend _ _ _) ()
  say-out _ _ _ (drecv _ _ _) ()
  say-out _ _ _ (esend _ _ _) ()
  say-out _ _ _ (erecv _ _ _) ()
  say-out _ _ _ (isend _ _ _) ()
  say-out _ _ _ (irecv _ _ _) ()
  say-out _ _ _ (choose _ _) ()
  say-out _ _ _ (branch _ _) ()
  say-out _ _ _ (pcase _ _) ()

  say-inn : ∀ A v ms S →
    accept (say inn A v ∷ ms) S ≡ true → Leg (say inn A v ∷ ms) S
  say-inn A v ms (recv B S) eq with ty≟ A B
  ... | yes′ refl =
    go-recv (proj₁ (∧-true eq)) (accept-sound ms S (proj₂ (∧-true eq)))
  ... | no′ _ = ⊥-from eq
    where
      ⊥-from : false ≡ true → Leg (say inn A v ∷ ms) (recv B S)
      ⊥-from ()
  say-inn _ _ _ end ()
  say-inn _ _ _ (send _ _) ()
  say-inn _ _ _ (dsend _ _ _) ()
  say-inn _ _ _ (drecv _ _ _) ()
  say-inn _ _ _ (esend _ _ _) ()
  say-inn _ _ _ (erecv _ _ _) ()
  say-inn _ _ _ (isend _ _ _) ()
  say-inn _ _ _ (irecv _ _ _) ()
  say-inn _ _ _ (choose _ _) ()
  say-inn _ _ _ (branch _ _) ()
  say-inn _ _ _ (pcase _ _) ()

  sel-out : ∀ b ms S →
    accept (sel out b ∷ ms) S ≡ true → Leg (sel out b ∷ ms) S
  sel-out b0 ms (choose S _) eq = go-c0 (accept-sound ms S eq)
  sel-out b1 ms (choose _ T) eq = go-c1 (accept-sound ms T eq)
  sel-out _ _ end ()
  sel-out _ _ (send _ _) ()
  sel-out _ _ (recv _ _) ()
  sel-out _ _ (dsend _ _ _) ()
  sel-out _ _ (drecv _ _ _) ()
  sel-out _ _ (esend _ _ _) ()
  sel-out _ _ (erecv _ _ _) ()
  sel-out _ _ (isend _ _ _) ()
  sel-out _ _ (irecv _ _ _) ()
  sel-out _ _ (branch _ _) ()
  sel-out _ _ (pcase _ _) ()

  sel-inn : ∀ b ms S →
    accept (sel inn b ∷ ms) S ≡ true → Leg (sel inn b ∷ ms) S
  sel-inn b0 ms (branch S _) eq = go-b0 (accept-sound ms S eq)
  sel-inn b1 ms (branch _ T) eq = go-b1 (accept-sound ms T eq)
  sel-inn _ _ end ()
  sel-inn _ _ (send _ _) ()
  sel-inn _ _ (recv _ _) ()
  sel-inn _ _ (dsend _ _ _) ()
  sel-inn _ _ (drecv _ _ _) ()
  sel-inn _ _ (esend _ _ _) ()
  sel-inn _ _ (erecv _ _ _) ()
  sel-inn _ _ (isend _ _ _) ()
  sel-inn _ _ (irecv _ _ _) ()
  sel-inn _ _ (choose _ _) ()
  sel-inn _ _ (pcase _ _) ()
