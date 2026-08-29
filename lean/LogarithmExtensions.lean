/-
  Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.

  LogarithmExtensions.lean — Branch Cuts, Recursive Log, Phase Functor
  ======================================================================
  Extends ComplexCore with:
  § 1  Branch-cut limits of principalLog at the negative real axis
  § 2  Recursive logarithm via Option monad (logStep, iterateOption)
  § 3  Fixed-point theorems for Complex.log
  § 4  Real exponential: no real fixed point, positivity, range, IVT
  § 5  Negative-imaginary phase functor (clockwise −90° / CCW 270°)
       with Boolean sign-predicate segment algebra and period-4 recursion

  References:
  [1]  Complex logarithm — Wikipedia https://wikipedia.org/wiki/Complex_logarithm
  [2]  How does a branch cut define a branch?
       https://math.stackexchange.com/questions/245579/how-does-a-branch-cut-define-a-branch
  [3]  The Logarithmic Function — Complex Analysis
       https://complex-analysis.com/content/logarithmic_function.html
  [4]  2.4 The Logarithmic Function — LibreTexts
       https://math.libretexts.org/Bookshelves/Analysis/Complex_Analysis_-_A_Visual_and_Interactive_Introduction_(Ponce_Campuzano)/02:_Chapter_2/2.04:_The_Logarithmic_Function
  [5]  The Monad Type Class — FPiL https://leanprover.github.io/functional_programming_in_lean/monads/class.html
  [6]  Recursive Definitions — Lean https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/
  [7]  Intermediate value theorem — Wikipedia https://en.wikipedia.org/wiki/Intermediate_value_theorem
  [8]  Mathlib IVT https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/IntermediateValue.html
  [9]  Complex logarithm — Continuity of Log z https://www.youtube.com/watch?v=GuUP-tCz2LI
  [10] Properties of Complex Logarithms — YouTube https://www.youtube.com/watch?v=sria1o3p6YY
  [11] Complex plane — Wikipedia https://en.wikipedia.org/wiki/Complex_plane
-/

import Mathlib.Analysis.Complex.Log
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

noncomputable section
open Real Complex Filter Set

namespace QautuamMath

-- re-use principalLog and phase from ComplexCore
def principalLog (z : ℂ) : ℂ :=
  (Real.log (Complex.abs z) : ℂ) + Complex.I * (Complex.arg z : ℂ)

def phase (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)

-- ===========================================================================
-- § 1  Branch-cut limits
-- ===========================================================================

/-- Approach (-r, 0) from above the cut. -/
def aboveCut (r t : ℝ) : ℂ := (-r : ℂ) + Complex.I * (t : ℂ)

/-- Approach (-r, 0) from below the cut. -/
def belowCut (r t : ℝ) : ℂ := (-r : ℂ) - Complex.I * (t : ℂ)

/-- Limit of principalLog from above: log r + iπ. -/
def upperCutLimit (r : ℝ) : ℂ := (Real.log r : ℂ) + Complex.I * (Real.pi : ℂ)

/-- Limit of principalLog from below: log r − iπ. -/
def lowerCutLimit (r : ℝ) : ℂ := (Real.log r : ℂ) - Complex.I * (Real.pi : ℂ)

/-- The jump across the branch cut is exactly 2πi. -/
theorem principalLog_branch_jump (r : ℝ) :
    upperCutLimit r - lowerCutLimit r =
      Complex.I * ((2 * Real.pi : ℝ) : ℂ) := by
  simp [upperCutLimit, lowerCutLimit]; ring

/-- The two one-sided limits are distinct (discontinuity at the cut). -/
theorem principalLog_branch_limits_ne (r : ℝ) :
    upperCutLimit r ≠ lowerCutLimit r := by
  intro h
  have him := congrArg Complex.im h
  simp [upperCutLimit, lowerCutLimit] at him
  linarith [Real.pi_pos]

/-- One-sided limit from above (analytic statement; component proofs are sorried
    pending Mathlib topology for Complex.arg continuity on half-planes). -/
theorem tendsto_principalLog_aboveCut (r : ℝ) (hr : 0 < r) :
    Tendsto (fun t : ℝ => principalLog (aboveCut r t))
      (𝓝[>] 0) (𝓝 (upperCutLimit r)) := by
  sorry

theorem tendsto_principalLog_belowCut (r : ℝ) (hr : 0 < r) :
    Tendsto (fun t : ℝ => principalLog (belowCut r t))
      (𝓝[>] 0) (𝓝 (lowerCutLimit r)) := by
  sorry

-- ===========================================================================
-- § 2  Recursive logarithm via Option monad
-- ===========================================================================

/-- One principal-log step; undefined at zero. -/
def logStep (z : ℂ) : Option ℂ :=
  if z = 0 then none else some (Complex.log z)

@[simp] theorem logStep_zero : logStep 0 = none := by simp [logStep]

@[simp] theorem logStep_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    logStep z = some (Complex.log z) := by simp [logStep, hz]

/-- Apply an Option-valued transition exactly n times. -/
def iterateOption (f : α → Option α) : ℕ → α → Option α
  | 0,     x => some x
  | n + 1, x => f x >>= iterateOption f n

/-- Iterated exact principal logarithm. -/
def recursiveLog : ℕ → ℂ → Option ℂ := iterateOption logStep

@[simp] theorem recursiveLog_zero (z : ℂ) :
    recursiveLog 0 z = some z := rfl

@[simp] theorem recursiveLog_succ (n : ℕ) (z : ℂ) :
    recursiveLog (n + 1) z = logStep z >>= recursiveLog n := rfl

theorem recursiveLog_succ_zero (n : ℕ) :
    recursiveLog (n + 1) 0 = none := by
  simp [recursiveLog, iterateOption, logStep]

theorem recursiveLog_succ_of_ne_zero (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    recursiveLog (n + 1) z = recursiveLog n (Complex.log z) := by
  simp [recursiveLog, iterateOption, logStep, hz]

/-- Iteration is compositional: m+n steps = m steps then n steps. -/
theorem iterateOption_add (f : α → Option α) (m n : ℕ) (x : α) :
    iterateOption f (m + n) x =
      iterateOption f m x >>= iterateOption f n := by
  induction m generalizing x with
  | zero => simp [iterateOption]
  | succ m ih =>
      simp [iterateOption, Nat.succ_add, ih]
      cases f x <;> simp [iterateOption]

theorem recursiveLog_add (m n : ℕ) (z : ℂ) :
    recursiveLog (m + n) z =
      recursiveLog m z >>= recursiveLog n :=
  iterateOption_add logStep m n z

/-- Guarded iterator parameterized by an admissibility predicate. -/
def guardedLogStep (admissible : ℂ → Prop) [DecidablePred admissible]
    (z : ℂ) : Option ℂ :=
  if admissible z then some (Complex.log z) else none

def recursiveGuardedLog (admissible : ℂ → Prop) [DecidablePred admissible] :
    ℕ → ℂ → Option ℂ :=
  iterateOption (guardedLogStep admissible)

-- ===========================================================================
-- § 3  Fixed-point theorems
-- ===========================================================================

/-- A complex fixed point of the principal logarithm. -/
def IsLogFixedPoint (z : ℂ) : Prop :=
  z ≠ 0 ∧ Complex.log z = z

/-- Fixed points satisfy exp z = z. -/
theorem exp_eq_self_of_log_fixedPoint {z : ℂ} (hz : IsLogFixedPoint z) :
    Complex.exp z = z := by
  rcases hz with ⟨hz0, hlog⟩
  rw [← hlog]; exact Complex.exp_log hz0

/-- Fixed points with the same components are equal. -/
theorem log_fixedPoint_ext {z w : ℂ}
    (_ : IsLogFixedPoint z) (_ : IsLogFixedPoint w)
    (hre : z.re = w.re) (him : z.im = w.im) : z = w :=
  Complex.ext hre him

def IsOptionFixedPoint (f : α → Option α) (x : α) : Prop := f x = some x

theorem iterateOption_fixedPoint {α : Type} (f : α → Option α) (x : α)
    (hfix : IsOptionFixedPoint f x) : ∀ n : ℕ, iterateOption f n x = some x := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp [iterateOption, hfix, ih]

theorem recursiveLog_fixedPoint (z : ℂ) (hfix : logStep z = some z) :
    ∀ n : ℕ, recursiveLog n z = some z :=
  iterateOption_fixedPoint logStep z hfix

theorem recursiveLog_stable_after (m n : ℕ) (z w : ℂ)
    (hreaches : recursiveLog m z = some w)
    (hfix : logStep w = some w) :
    recursiveLog (m + n) z = some w := by
  rw [recursiveLog_add, hreaches]
  simp only [Option.some_bind]
  exact recursiveLog_fixedPoint w hfix n

-- ===========================================================================
-- § 4  Real exponential: no fixed point, positivity, range, IVT
-- ===========================================================================

/-- exp x + 1 ≤ exp x forces exp x ≠ x. -/
theorem real_exp_ne_self (x : ℝ) : Real.exp x ≠ x := by
  intro h
  have : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  linarith

/-- exp is strictly positive everywhere. -/
theorem real_exp_pos' (x : ℝ) : 0 < Real.exp x := Real.exp_pos x

theorem real_exp_ne_zero' (x : ℝ) : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)

/-- A complex number with zero imaginary part cannot be a fixed point of exp. -/
theorem complex_exp_eq_self_no_real_solution (z : ℂ) (hz : z.im = 0) :
    Complex.exp z ≠ z := by
  intro h
  have hre : Real.exp z.re = z.re := by
    have := congrArg Complex.re h
    simpa [Complex.exp_re, hz] using this
  exact real_exp_ne_self z.re hre

/-- Range of Real.exp is exactly the positive reals. -/
theorem range_real_exp : Set.range Real.exp = Set.Ioi (0 : ℝ) := by
  ext y; constructor
  · rintro ⟨x, rfl⟩; exact Real.exp_pos x
  · intro hy; exact ⟨Real.log y, Real.exp_log hy⟩

/-- IVT: if exp a ≤ y ≤ exp b then y is attained on [a, b]. -/
theorem exists_exp_eq_of_between (a b y : ℝ) (hab : a ≤ b)
    (hay : Real.exp a ≤ y) (hyb : y ≤ Real.exp b) :
    ∃ x ∈ Set.Icc a b, Real.exp x = y :=
  intermediate_value_Icc hab Real.continuous_exp.continuousOn hay hyb

/-- For any positive y, a preimage exists (short direct proof). -/
theorem exists_exp_eq_of_pos (y : ℝ) (hy : 0 < y) :
    ∃ x : ℝ, Real.exp x = y :=
  ⟨Real.log y, Real.exp_log hy⟩

/-- Surjectivity of exp onto positive reals. -/
theorem real_exp_surjective_positive :
    Function.Surjective
      (fun x : ℝ => ⟨Real.exp x, Real.exp_pos x⟩ : ℝ → Set.Ioi (0 : ℝ)) := by
  intro y; exact ⟨Real.log y.1, Subtype.ext (Real.exp_log y.2)⟩

theorem log_exp_inverse (x : ℝ) : Real.log (Real.exp x) = x := Real.log_exp x
theorem exp_log_inverse (y : ℝ) (hy : 0 < y) : Real.exp (Real.log y) = y := Real.exp_log hy

-- ===========================================================================
-- § 5  Negative-imaginary phase functor and Boolean segment algebra
-- ===========================================================================

/-- Clockwise quarter-turn: multiplication by −i. -/
def negImagFunctor (z : ℂ) : ℂ := (-Complex.I) * z

/-- −i is the clockwise quarter-turn phase. -/
theorem negImagFunctor_eq_phase :
    (-Complex.I : ℂ) = phase (-(Real.pi / 2)) := by
  simp [phase]

/-- CW 90° = CCW 270°: both give −i. -/
theorem clockwise90_eq_counterclockwise270 :
    phase (-(Real.pi / 2)) = phase (3 * Real.pi / 2) := by
  simp [phase]

/-- Component action: (a+bi) · (−i) = b − ai. -/
@[simp] theorem negImagFunctor_re (z : ℂ) : (negImagFunctor z).re = z.im := by
  simp [negImagFunctor]

@[simp] theorem negImagFunctor_im (z : ℂ) : (negImagFunctor z).im = -z.re := by
  simp [negImagFunctor]

theorem negImagFunctor_components (z : ℂ) :
    negImagFunctor z = (z.im : ℂ) - Complex.I * (z.re : ℂ) := by
  unfold negImagFunctor; apply Complex.ext <;> simp

/-- For a positive real x, negImagFunctor maps it to −xi (negative imaginary axis). -/
theorem negImagFunctor_real (x : ℝ) :
    negImagFunctor (x : ℂ) = -(x : ℂ) * Complex.I := by
  simp [negImagFunctor]; ring

-- ---- Boolean segment predicates (quadrant labels) ----

def IsUpper    (z : ℂ) : Prop := 0 < z.im
def IsLower    (z : ℂ) : Prop := z.im < 0
def IsRealAxis (z : ℂ) : Prop := z.im = 0

/-- A positive real maps to the negative imaginary axis (lower half-plane). -/
theorem negImagFunctor_of_positive_real (x : ℝ) (hx : 0 < x) :
    IsLower (negImagFunctor (x : ℂ)) := by
  simp [IsLower, negImagFunctor_im, hx]

-- ---- Recursive rotation and period-4 law ----

/-- Apply the clockwise quarter-turn n times. -/
def recurseNegImag : ℕ → ℂ → ℂ
  | 0,     z => z
  | n + 1, z => negImagFunctor (recurseNegImag n z)

@[simp] theorem recurseNegImag_zero (z : ℂ) : recurseNegImag 0 z = z := rfl
@[simp] theorem recurseNegImag_succ (n : ℕ) (z : ℂ) :
    recurseNegImag (n + 1) z = negImagFunctor (recurseNegImag n z) := rfl

/-- Four clockwise quarter-turns = identity: (−i)⁴ = 1. -/
theorem recurseNegImag_four (z : ℂ) : recurseNegImag 4 z = z := by
  simp [recurseNegImag, negImagFunctor]; ring

/-- The period is exactly 4. -/
theorem recurseNegImag_period (z : ℂ) (n : ℕ) :
    recurseNegImag (n + 4) z = recurseNegImag n z := by
  induction n with
  | zero => exact recurseNegImag_four z
  | succ n ih =>
      simp only [recurseNegImag_succ]
      rw [show n + 1 + 4 = (n + 4) + 1 by ring]
      simp only [recurseNegImag_succ]
      rw [ih]

/-
  Hand-written Boolean-algebra proof of the period-4 law (companion to the Lean proof):

  Let σ(t) = 0 if t ≥ 0, 1 if t < 0 (Boolean sign predicate).
  For z = a + bi, the sign pair is (σ(a), σ(b)).

  One application of F(z) = −iz maps (a, b) ↦ (b, −a), so:
    sign pair:  (σ(a), σ(b)) ↦ (σ(b), ¬σ(a))

  Iterating:
    n=0: (σ(a),  σ(b))
    n=1: (σ(b),  ¬σ(a))
    n=2: (¬σ(a), ¬σ(b))
    n=3: (¬σ(b),  σ(a))
    n=4: (σ(a),   σ(b))   ← returns to start

  Uses only: ¬¬x = x (double negation), commutativity.
  This is the Boolean-algebraic certificate that (−i)⁴ = 1.
-/

-- ===========================================================================
-- § 6  Quadrant-II imaginary construction and three hypercomplex geometries
-- ===========================================================================

/-
  Hand-written algebraic construction (companion to the Lean theorems below):

  For r > 0 the elementary identity (i√r)² = −r places the positive imaginary
  square root of −r on the positive imaginary axis. Adding a small negative real
  part ε > 0 shifts the point into quadrant II:

      z_ε = −ε + iy   (ε > 0, y > 0)

  Squaring:  z_ε² = ε² − y² − 2iεy
  As ε → 0⁺:  z_ε² → −y² (a negative real, imaginary part → 0⁻)

  Hence the positive imaginary component y is the positive square-root of |−y²|.
  The cross-term −2iεy carries the sign information used by the phase functor.

  The three isomorphic hypercomplex geometries (varying the square of the unit):
    k = −1 : Complex numbers  ℂ,  i² = −1  (elliptic, rotation, period-4 functor)
    k =  0 : Dual numbers     𝔻,  ε² =  0  (parabolic, shear, exact O(N) AutoDiff)
    k = +1 : Split-complex    𝕊,  j² = +1  (hyperbolic, Lorentz boost)

  In characteristic 2 (𝔽₂), the cross-term −2iεy vanishes identically because
  2 ≡ 0 (mod 2), collapsing the entire imaginary phase space to deterministic
  Boolean XOR/AND — the hardware-native form.
-/

/-- The elementary square-root identity: (i√r)² = −r. -/
theorem imaginary_sqrt_sq (r : ℝ) (hr : 0 ≤ r) :
    (Complex.I * (Real.sqrt r : ℂ)) ^ 2 = -(r : ℂ) := by
  simp [mul_pow, Complex.I_sq, Real.sq_sqrt hr]
  ring

/-- Squaring z_ε = −ε + iy: real part = ε²−y², imaginary part = −2εy. -/
theorem quadrant_II_sq_re (ε y : ℝ) :
    ((-ε : ℂ) + Complex.I * (y : ℂ)) ^ 2 |>.re = ε ^ 2 - y ^ 2 := by
  simp [sq, Complex.mul_re, Complex.add_re]; ring

theorem quadrant_II_sq_im (ε y : ℝ) :
    ((-ε : ℂ) + Complex.I * (y : ℂ)) ^ 2 |>.im = -2 * ε * y := by
  simp [sq, Complex.mul_im, Complex.add_im]; ring

/-- As ε → 0, the imaginary part of z_ε² → 0. -/
theorem quadrant_II_sq_im_tendsto (y : ℝ) :
    Tendsto (fun ε : ℝ => -2 * ε * y) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun ε : ℝ => -2 * ε * y) (𝓝 0) (𝓝 0) := by
    have := (continuousAt_id.const_mul (-2)).mul continuousAt_const
    simpa using this.tendsto
  exact this.mono_left nhdsWithin_le_nhds

/-- As ε → 0, the real part of z_ε² → −y². -/
theorem quadrant_II_sq_re_tendsto (y : ℝ) :
    Tendsto (fun ε : ℝ => ε ^ 2 - y ^ 2) (𝓝[>] 0) (𝓝 (-y ^ 2)) := by
  have : Tendsto (fun ε : ℝ => ε ^ 2 - y ^ 2) (𝓝 0) (𝓝 (-y ^ 2)) := by
    have h := (continuous_pow 2).continuousAt (x := (0 : ℝ))
    simp at h
    exact h.sub continuousAt_const |>.congr (by simp) |>.tendsto
  exact this.mono_left nhdsWithin_le_nhds

/-- The phase functor F sends a quadrant-II point to quadrant I. -/
theorem negImagFunctor_quadrant_II_to_I (ε y : ℝ) (hε : 0 < ε) (hy : 0 < y) :
    0 < (negImagFunctor ((-ε : ℂ) + Complex.I * (y : ℂ))).re ∧
    0 < (negImagFunctor ((-ε : ℂ) + Complex.I * (y : ℂ))).im := by
  constructor
  · simp [negImagFunctor, Complex.add_re, Complex.mul_re]; linarith
  · simp [negImagFunctor, Complex.add_im, Complex.mul_im]; linarith

end QautuamMath
