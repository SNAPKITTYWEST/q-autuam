{-# OPTIONS --without-K --safe #-}
-- Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.
-- Patent Pending.
--
-- TPE1.SHA256.Invariants — Agda structural specification
-- Corrects the persona's NotSingular guard from (b ∨ cin) to (b ≢ cin).
-- See Lean TopologicalVerification.lean §11 for verified truth table.

module TPE1.SHA256.Invariants where

open import Data.Bool using (Bool; true; false; not)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

-- ---------------------------------------------------------------------------
-- § Primitives (𝔽₂)
-- ---------------------------------------------------------------------------

_⊕_ : Bool → Bool → Bool
true  ⊕ false = true
false ⊕ true  = true
_     ⊕ _     = false

t∧ : Bool → Bool → Bool
t∧ true true = true
t∧ _    _    = false

carry-knot : Bool → Bool → Bool → Bool
carry-knot a b cin = (t∧ a b) ⊕ (t∧ cin (a ⊕ b))

-- Witness: exact translation of Lean carry_knot_reversible_of_ne
-- At (F,F) singularity no witness for out=true; at (T,T) witness is not out
witness : Bool → Bool → Bool → Bool
witness true  true  out = not out
witness true  false out = out
witness false true  out = out
witness false false _   = false

-- ---------------------------------------------------------------------------
-- § Invariant 1: Singularity Horizon
-- ---------------------------------------------------------------------------

invariant-singularity-erasure : (a : Bool) → carry-knot a false false ≡ false
invariant-singularity-erasure false = refl
invariant-singularity-erasure true  = refl

invariant-singularity-saturation : (a : Bool) → carry-knot a true true ≡ true
invariant-singularity-saturation false = refl
invariant-singularity-saturation true  = refl

IsSingular : Bool → Bool → Set
IsSingular b cin = b ≡ cin

-- ---------------------------------------------------------------------------
-- § Invariant 2: Deterministic reversibility on ¬singular (b ≢ cin)
-- ---------------------------------------------------------------------------

record NotSingular (b cin : Bool) : Set where
  field
    b≢cin : ¬ (b ≡ cin)

-- Persona's original guard (b≡false → cin≡false → ⊥) ≡ b∨cin is insufficient:
-- counterexample (T,T) with out=false has no witness yet satisfies b∨cin.

invariant-reversibility-true-false-true : carry-knot (witness true false true) true false ≡ true
invariant-reversibility-true-false-true = refl

invariant-reversibility-true-false-false : carry-knot (witness true false false) true false ≡ false
invariant-reversibility-true-false-false = refl

invariant-reversibility-false-true-true : carry-knot (witness false true true) false true ≡ true
invariant-reversibility-false-true-true = refl

invariant-reversibility-false-true-false : carry-knot (witness false true false) false true ≡ false
invariant-reversibility-false-true-false = refl

invariant-reversibility : (b cin out : Bool) → NotSingular b cin → carry-knot (witness b cin out) b cin ≡ out
invariant-reversibility true  false true  ns = refl
invariant-reversibility true  false false ns = refl
invariant-reversibility false true  true  ns = refl
invariant-reversibility false true  false ns = refl
invariant-reversibility false false out record { b≢cin = p } = ⊥-elim (p refl)
invariant-reversibility true  true  out record { b≢cin = p } = ⊥-elim (p refl)

-- ---------------------------------------------------------------------------
-- § Invariant 3: Unrolling chain
-- ---------------------------------------------------------------------------

record State : Set where
  field
    b   : Bool
    cin : Bool
    out : Bool

unroll-step : State → Bool
unroll-step s = witness (State.b s) (State.cin s) (State.out s)

invariant-unroll : (s : State) → NotSingular (State.b s) (State.cin s) →
                   carry-knot (unroll-step s) (State.b s) (State.cin s) ≡ State.out s
invariant-unroll s ns = invariant-reversibility (State.b s) (State.cin s) (State.out s) ns

-- ---------------------------------------------------------------------------
-- § Honest accounting
-- ---------------------------------------------------------------------------
-- Proves forward correctness + witness inverse on b≢cin.
-- Does NOT prove O(1) preimage, holographic O(1) projection, or any
-- break of SHA-256 one-wayness. See lean/TopologicalVerification.lean,
-- src/topological/complexity_budget.rs, spec/topological/TOPOLOGICAL_SAT_SPEC.md
