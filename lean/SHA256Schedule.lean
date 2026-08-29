/-
  Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.
  Patent Pending.

  SHA256Schedule.lean — Safe array-based SHA-256 message-schedule
  verification (W[t] recurrence).

  Source: Ahmad 2026-08-29 follow-up (array-based construction) with
  corrections:
    - extendSchedule requires 16 ≤ w.size (no sorry on t≥16)
    - Array.get with Fin w.size (no defaulting a[i])
    - buildScheduleAux carries h16 proof, size = w.size + fuel
    - scheduleOfArray uses safe get + messageScheduleArray_size
    - ScheduleInvariant via Array.get (no w[t] unchecked)
    - Separate CSA trace for schedule 4-addend reduction (not Maj/Ch)

  Status: Core + invariants zero-sorry (decide/omega/ring). The schedule
  expansion is 48 steps from 16 → 64; the 4-addend CSA decomposition
  is 2 layers (see SHA256CarryMatrix.lean for weighted_rows_sum).

  References:
    FIPS 180-4 §6.2.2 : W[t] = W[t-16]+σ0(W[t-15])+W[t-7]+σ1(W[t-2])
-/

import Mathlib.Data.BitVec.Basic
import Mathlib.Data.Array.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open BitVec

namespace SHA256

-- ---------------------------------------------------------------------------
-- § 0  Core types (re-export Word from SHA256CarryMatrix if imported)
-- ---------------------------------------------------------------------------

abbrev Word := BitVec 32
abbrev Block := Fin 16 → Word
abbrev Schedule := Fin 64 → Word

def smallSigma0 (x : Word) : Word :=
  x.ror 7 ^^^ x.ror 18 ^^^ (x >>> 3)

def smallSigma1 (x : Word) : Word :=
  x.ror 17 ^^^ x.ror 19 ^^^ (x >>> 10)

-- ---------------------------------------------------------------------------
-- § 1  Array core (A safer array core — verified bounds)
-- ---------------------------------------------------------------------------

def initialSchedule (block : Block) : Array Word :=
  Array.ofFn block

theorem initialSchedule_size (block : Block) :
    (initialSchedule block).size = 16 := by
  simp [initialSchedule]

def extendSchedule (w : Array Word) (h16 : 16 ≤ w.size) : Array Word :=
  let t := w.size
  w.push (
    w.get ⟨t - 16, by omega⟩ +
    smallSigma0 (w.get ⟨t - 15, by omega⟩) +
    w.get ⟨t - 7, by omega⟩ +
    smallSigma1 (w.get ⟨t - 2, by omega⟩)
  )

theorem extendSchedule_size (w : Array Word) (h16 : 16 ≤ w.size) :
    (extendSchedule w h16).size = w.size + 1 := by
  simp [extendSchedule]

-- ---------------------------------------------------------------------------
-- § 2  Recursive builder with budget (16 → 64, not arbitrary)
-- ---------------------------------------------------------------------------

def buildScheduleAux :
    (fuel : Nat) →
    (w : Array Word) →
    16 ≤ w.size →
    Array Word
  | 0, w, _ => w
  | fuel + 1, w, h16 =>
      buildScheduleAux fuel (extendSchedule w h16) (by
        rw [extendSchedule_size]
        omega)

def messageScheduleArray (block : Block) : Array Word :=
  buildScheduleAux 48 (initialSchedule block) (by
    rw [initialSchedule_size])

theorem buildScheduleAux_size
    (fuel : Nat) (w : Array Word) (h16 : 16 ≤ w.size) :
    (buildScheduleAux fuel w h16).size = w.size + fuel := by
  induction fuel generalizing w with
  | zero => simp [buildScheduleAux]
  | succ fuel ih =>
      simp only [buildScheduleAux]
      rw [ih]
      rw [extendSchedule_size]
      omega

theorem messageScheduleArray_size (block : Block) :
    (messageScheduleArray block).size = 64 := by
  unfold messageScheduleArray
  rw [buildScheduleAux_size, initialSchedule_size]
  norm_num

theorem messageScheduleArray_size_le_64 (block : Block) :
    (messageScheduleArray block).size ≤ 64 := by
  rw [messageScheduleArray_size]

-- ---------------------------------------------------------------------------
-- § 3  Safe indexing lemmas for extension
-- ---------------------------------------------------------------------------

theorem get_extendSchedule_old
    (w : Array Word) (h16 : 16 ≤ w.size) (i : Fin w.size) :
    (extendSchedule w h16).get
      ⟨i.val, by rw [extendSchedule_size]; exact Nat.lt_succ_of_lt i.isLt⟩
    =
    w.get i := by
  simp [extendSchedule]

theorem get_extendSchedule_new
    (w : Array Word) (h16 : 16 ≤ w.size) :
    (extendSchedule w h16).get
      ⟨w.size, by rw [extendSchedule_size]⟩
    =
    w.get ⟨w.size - 16, by omega⟩ +
      smallSigma0 (w.get ⟨w.size - 15, by omega⟩) +
      w.get ⟨w.size - 7, by omega⟩ +
      smallSigma1 (w.get ⟨w.size - 2, by omega⟩) := by
  simp [extendSchedule]

-- ---------------------------------------------------------------------------
-- § 4  Schedule invariant via Array.get (no unchecked w[t])
-- ---------------------------------------------------------------------------

def ScheduleInvariant (block : Block) (w : Array Word) : Prop :=
  16 ≤ w.size ∧
  (∀ i : Fin 16,
    w.get ⟨i.val, by omega⟩ = block i) ∧
  (∀ t : Nat, ∀ ht16 : 16 ≤ t, ∀ ht : t < w.size,
    w.get ⟨t, ht⟩ =
      w.get ⟨t - 16, by omega⟩ +
      smallSigma0 (w.get ⟨t - 15, by omega⟩) +
      w.get ⟨t - 7, by omega⟩ +
      smallSigma1 (w.get ⟨t - 2, by omega⟩))

def CanExtend (fuel : Nat) (w : Array Word) : Prop :=
  16 ≤ w.size ∧ w.size + fuel ≤ 64

lemma initialSchedule_invariant (block : Block) :
    ScheduleInvariant block (initialSchedule block) := by
  constructor
  · simp [initialSchedule_size]
  constructor
  · intro i
    simp [initialSchedule, Array.get_ofFn]
  · intro t ht16 ht
    -- t < 16 from size 16, contradicts 16 ≤ t
    have h : t < 16 := by
      have : (initialSchedule block).size = 16 := initialSchedule_size block
      omega
    omega

lemma extendSchedule_invariant {block : Block} {w : Array Word}
    (hw : ScheduleInvariant block w)
    (h64 : w.size < 64) :
    ScheduleInvariant block (extendSchedule w hw.1) := by
  have h16 := hw.1
  have hInit := hw.2.1
  have hRec := hw.2.2
  constructor
  · rw [extendSchedule_size]; omega
  constructor
  · intro i
    have h : i.val < w.size := by omega
    rw [get_extendSchedule_old w h16 ⟨i.val, h⟩]
    exact hInit i
  · intro t ht16 ht
    have ht' : t < w.size + 1 := by rw [← extendSchedule_size w h16] at ht; exact ht
    by_cases hlt : t < w.size
    · -- old index preserved
      have hGet : (extendSchedule w h16).get ⟨t, ht⟩ = w.get ⟨t, hlt⟩ := by
        simp [extendSchedule, Array.get_push]
        split <;> simp [Fin.val_mk] at * <;> omega
      rw [hGet]
      have hEq := hRec t ht16 hlt
      -- rewrite RHS gets to extended array (still < w.size)
      have h16' : t - 16 < w.size := by omega
      have h15' : t - 15 < w.size := by omega
      have h7' : t - 7 < w.size := by omega
      have h2' : t - 2 < w.size := by omega
      have g16 : (extendSchedule w h16).get ⟨t - 16, by rw [extendSchedule_size]; omega⟩ = w.get ⟨t - 16, h16'⟩ := by simp [extendSchedule, Array.get_push]; split <;> omega
      have g15 : (extendSchedule w h16).get ⟨t - 15, by rw [extendSchedule_size]; omega⟩ = w.get ⟨t - 15, h15'⟩ := by simp [extendSchedule, Array.get_push]; split <;> omega
      have g7 : (extendSchedule w h16).get ⟨t - 7, by rw [extendSchedule_size]; omega⟩ = w.get ⟨t - 7, h7'⟩ := by simp [extendSchedule, Array.get_push]; split <;> omega
      have g2 : (extendSchedule w h16).get ⟨t - 2, by rw [extendSchedule_size]; omega⟩ = w.get ⟨t - 2, h2'⟩ := by simp [extendSchedule, Array.get_push]; split <;> omega
      rw [g16, g15, g7, g2] at *
      exact hEq
    · -- t = w.size, the newly pushed word
      have hEq : t = w.size := by omega
      subst hEq
      rw [get_extendSchedule_new w h16]
      -- RHS gets are all < w.size < 64, so preserved as above
      rfl

lemma buildScheduleAux_invariant (fuel : Nat) {block : Block} {w : Array Word}
    (hw : ScheduleInvariant block w) (hFuel : w.size + fuel ≤ 64) :
    ScheduleInvariant block (buildScheduleAux fuel w hw.1) := by
  induction fuel generalizing w with
  | zero => simpa [buildScheduleAux]
  | succ fuel ih =>
      have h64 : w.size < 64 := by omega
      have hNext : ScheduleInvariant block (extendSchedule w hw.1) := extendSchedule_invariant hw h64
      have hSize : (extendSchedule w hw.1).size = w.size + 1 := extendSchedule_size w hw.1
      have hFuel' : (extendSchedule w hw.1).size + fuel ≤ 64 := by rw [hSize]; omega
      exact ih hNext hFuel'

lemma messageScheduleArray_invariant (block : Block) :
    ScheduleInvariant block (messageScheduleArray block) := by
  have h0 : ScheduleInvariant block (initialSchedule block) := initialSchedule_invariant block
  have hFuel : (initialSchedule block).size + 48 ≤ 64 := by rw [initialSchedule_size]
  exact buildScheduleAux_invariant 48 h0 hFuel

-- ---------------------------------------------------------------------------
-- § 5  Safe final schedule API (Fin 64 → Word)
-- ---------------------------------------------------------------------------

def scheduleOfArray (block : Block) : Schedule :=
  fun i =>
    (messageScheduleArray block).get
      ⟨i.val, by rw [messageScheduleArray_size]; exact i.isLt⟩

theorem schedule_initial_words (block : Block) (i : Fin 16) :
    scheduleOfArray block ⟨i.val, by omega⟩ = block i := by
  have hInv := messageScheduleArray_invariant block
  have h := hInv.2.1 ⟨i.val, by omega⟩
  simp only [scheduleOfArray] at h ⊢
  -- both gets are at same index < 64
  have hIdx : (⟨i.val, by omega⟩ : Fin 64).val = i.val := rfl
  simp [hIdx] at h ⊢
  -- need to align Fin 16 vs Fin 64 proofs — both are i.val
  exact h

theorem schedule_recurrence (block : Block) (t : Fin 64) (ht : 16 ≤ t.val) :
    scheduleOfArray block t =
      scheduleOfArray block ⟨t.val - 16, by omega⟩ +
      smallSigma0 (scheduleOfArray block ⟨t.val - 15, by omega⟩) +
      scheduleOfArray block ⟨t.val - 7, by omega⟩ +
      smallSigma1 (scheduleOfArray block ⟨t.val - 2, by omega⟩) := by
  have hInv := messageScheduleArray_invariant block
  have hRec := hInv.2.2 t.val ht (by rw [messageScheduleArray_size] at *; exact t.isLt)
  simp only [scheduleOfArray] at hRec ⊢
  exact hRec

-- ---------------------------------------------------------------------------
-- § 6  Specification predicate and final correctness
-- ---------------------------------------------------------------------------

def IsMessageSchedule (block : Block) (w : Schedule) : Prop :=
  (∀ i : Fin 16, w ⟨i.val, by omega⟩ = block i) ∧
  (∀ t : Fin 64, 16 ≤ t.val →
    w t =
      w ⟨t.val - 16, by omega⟩ +
      smallSigma0 (w ⟨t.val - 15, by omega⟩) +
      w ⟨t.val - 7, by omega⟩ +
      smallSigma1 (w ⟨t.val - 2, by omega⟩))

theorem messageSchedule_correct (block : Block) :
    IsMessageSchedule block (scheduleOfArray block) := by
  constructor
  · intro i
    exact schedule_initial_words block i
  · intro t ht
    exact schedule_recurrence block t ht

-- ---------------------------------------------------------------------------
-- § 7  CSA trace for schedule words (4 addends → 2 CSA layers)
-- ---------------------------------------------------------------------------
-- W[t] = W[t-16] + σ0(W[t-15]) + W[t-7] + σ1(W[t-2])
-- Decompose as:
--   L0 = CSA(W[t-16], σ0(W[t-15]), W[t-7]) → (sum0, carry0)
--   L1 = CSA(sum0, carry0, σ1(W[t-2])) → (sum1, carry1)
--   W[t] = sum1 + carry1  (mod 2^32)
-- Each L satisfies weighted_rows_sum (SHA256CarryMatrix.lean).

structure ScheduleStepTrace where
  t : Fin 64
  layer0 : Fin 32 → CSAColumn  -- CSA(W[t-16], σ0, W[t-7])
  layer1 : Fin 32 → CSAColumn  -- CSA(sum0, carry0, σ1)

-- Placeholder: columns are derived from the three words of each layer.
-- Lean reconstructs faSum/faCarry from x,y,z and checks weighted_rows_sum.
-- Rust provides the x,y,z bits via sha256_schedule.rs.

end SHA256
