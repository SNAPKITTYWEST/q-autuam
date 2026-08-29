/-
  Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.

  TrigCore.lean — Chebyshev Polynomial Correctness
  ==================================================
  Proves T_n(cos θ) = cos(n·θ) via coupled cosCore/sinCore induction.

  Strategy: define cosCore and sinCore via the classical three-term recurrence,
  prove them simultaneously by two-step induction using angle-addition formulae.

  References:
  [1] Proofs of trigonometric identities — Wikipedia
      https://en.wikipedia.org/wiki/Proofs_of_trigonometric_identities
  [2] Deriving Sum/Difference Identities for Cosine — YouTube
      https://www.youtube.com/watch?v=XfS5UZQca0g
  [3] (cos θ + i sin θ)^n = cos nθ + i sin nθ — YouTube
      https://www.youtube.com/watch?v=On1n4l-ki5I
  [4] Identities on cos(nθ) and sin(nθ) — Math StackExchange
      https://math.stackexchange.com/questions/1255215/identities-on-cos-n-theta-and-sin-n-theta
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section
open Real

namespace QautuamMath

-- ---------------------------------------------------------------------------
-- § 1 — Chebyshev-style recurrences
-- ---------------------------------------------------------------------------

/-- Cosine component of the recursive trig state (Chebyshev T_n). -/
def cosCore (θ : ℝ) : ℕ → ℝ
  | 0     => 1
  | 1     => Real.cos θ
  | n + 2 => 2 * Real.cos θ * cosCore θ (n + 1) - cosCore θ n

/-- Sine component: U_{n-1}(cos θ) · sin θ in disguise. -/
def sinCore (θ : ℝ) : ℕ → ℝ
  | 0     => 0
  | 1     => Real.sin θ
  | n + 2 => 2 * Real.cos θ * sinCore θ (n + 1) - sinCore θ n

-- Simp lemmas for the recurrences
@[simp] theorem cosCore_zero (θ : ℝ) : cosCore θ 0 = 1 := rfl
@[simp] theorem cosCore_one  (θ : ℝ) : cosCore θ 1 = Real.cos θ := rfl

@[simp] theorem sinCore_zero (θ : ℝ) : sinCore θ 0 = 0 := rfl
@[simp] theorem sinCore_one  (θ : ℝ) : sinCore θ 1 = Real.sin θ := rfl

@[simp] theorem cosCore_succ_succ (θ : ℝ) (n : ℕ) :
    cosCore θ (n + 2) =
      2 * Real.cos θ * cosCore θ (n + 1) - cosCore θ n := rfl

@[simp] theorem sinCore_succ_succ (θ : ℝ) (n : ℕ) :
    sinCore θ (n + 2) =
      2 * Real.cos θ * sinCore θ (n + 1) - sinCore θ n := rfl

-- ---------------------------------------------------------------------------
-- § 2 — Coupled invariant
-- ---------------------------------------------------------------------------

/-- The joint closed-form property: cos recurrence = cos(nθ), sin recurrence = sin(nθ). -/
def TrigInvariant (θ : ℝ) (n : ℕ) : Prop :=
  cosCore θ n = Real.cos ((n : ℝ) * θ) ∧
  sinCore θ n = Real.sin ((n : ℝ) * θ)

-- ---------------------------------------------------------------------------
-- § 3 — Main theorem: T_n(cos θ) = cos(n·θ)
-- ---------------------------------------------------------------------------

/--
  Coupled induction proof of the closed form.
  Uses angle-addition formulae:
    cos(a+b) = cos a cos b − sin a sin b
    sin(a+b) = sin a cos b + cos a sin b
-/
theorem trigCore_closed_form (θ : ℝ) (n : ℕ) : TrigInvariant θ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor
      · simp [cosCore]
      · simp [sinCore]
  | one =>
      constructor
      · simp [cosCore]
      · simp [sinCore]
  | more n ihN ihN1 =>
      rcases ihN  with ⟨hcN,  hsN⟩
      rcases ihN1 with ⟨hcN1, hsN1⟩
      constructor
      · -- cosCore θ (n+2) = cos((n+2)·θ)
        simp only [cosCore_succ_succ]
        rw [hcN, hcN1]
        -- cos((n+2)·θ) = 2cos θ · cos((n+1)·θ) − cos(n·θ)
        have : Real.cos (((n : ℝ) + 2) * θ) =
               2 * Real.cos θ * Real.cos (((n : ℝ) + 1) * θ) -
               Real.cos ((n : ℝ) * θ) := by
          have h1 : ((n : ℝ) + 2) * θ = ((n : ℝ) + 1) * θ + θ := by ring
          have h2 : ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ     := by ring
          rw [h1, Real.cos_add, h2, Real.cos_add, Real.sin_add]
          have sq := Real.sin_sq_add_cos_sq θ
          ring_nf
          nlinarith [Real.sin_sq_add_cos_sq θ]
        linarith [this]
      · -- sinCore θ (n+2) = sin((n+2)·θ)
        simp only [sinCore_succ_succ]
        rw [hsN, hsN1]
        have : Real.sin (((n : ℝ) + 2) * θ) =
               2 * Real.cos θ * Real.sin (((n : ℝ) + 1) * θ) -
               Real.sin ((n : ℝ) * θ) := by
          have h1 : ((n : ℝ) + 2) * θ = ((n : ℝ) + 1) * θ + θ := by ring
          have h2 : ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ     := by ring
          rw [h1, Real.sin_add, h2, Real.cos_add, Real.sin_add]
          have sq := Real.sin_sq_add_cos_sq θ
          ring_nf
          nlinarith [Real.sin_sq_add_cos_sq θ]
        linarith [this]

-- ---------------------------------------------------------------------------
-- § 4 — Clean corollaries
-- ---------------------------------------------------------------------------

/-- Primary Chebyshev identity: T_n(cos θ) = cos(n·θ). -/
theorem T_cos (n : ℕ) (θ : ℝ) :
    cosCore θ n = Real.cos ((n : ℝ) * θ) :=
  (trigCore_closed_form θ n).1

/-- Companion identity: sin recurrence matches sin(n·θ). -/
theorem S_sin (n : ℕ) (θ : ℝ) :
    sinCore θ n = Real.sin ((n : ℝ) * θ) :=
  (trigCore_closed_form θ n).2

-- Special cases
lemma T_two (x : ℝ) : cosCore x 2 = 2 * x ^ 2 - 1 := by
  simp [cosCore]; ring

lemma T_two_cos (θ : ℝ) : cosCore θ 2 = Real.cos (2 * θ) := by
  rw [T_two]
  rw [Real.cos_two_mul]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

end QautuamMath
