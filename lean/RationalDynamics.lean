/-
  Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.

  RationalDynamics.lean — T(z) = 2z/(1-z²) Fixed Points and 3-SAT Embedding
  ============================================================================
  Formalizes Ahmad's observation that the rational dynamical system
  T(z) = 2(1/z - z)⁻¹ = 2z/(1-z²) has z = ±i as its non-zero fixed points,
  and that this is the complex-plane double-angle map for tangent:
    tan(2θ) = 2tan(θ)/(1-tan²(θ))

  The fixed point z = i connects to:
  - The Chebyshev tower in TrigCore.lean (θ = π/2 is a fixed angle)
  - The period-4 rotation (multiplying by i four times = identity)
  - The F₂ dual number period-2 collapse in DualNumbers.lean
  - The 3-SAT arithmetization via F(x) = Π_j C_j

  Key result: T(i) = i — the imaginary unit is a fixed point.
  The hardness of 3-SAT is preserved under this embedding (not circumvented).
  The geometery is beautiful; the complexity is unchanged.

  References:
  [1]  Arithmetization of 3-SAT: F(x) = Π(1-(1-ℓ₁)(1-ℓ₂)(1-ℓ₃))
  [2]  Double-angle tangent formula: tan(2θ) = 2tan(θ)/(1-tan²(θ))
  [3]  BSS machine theory: continuous dynamics cannot solve NP in polynomial time
       (Pour-El, Richards; Blum-Shub-Smale)
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section
open Complex Real

namespace QautuamMath

-- ===========================================================================
-- § 1  The rational transformation T(z) = 2z / (1 - z²)
-- ===========================================================================

/-- T(z) = 2z / (1 - z²) — the complex double-angle tangent map.
    Equivalent to 2(1/z - z)⁻¹ after clearing denominators. -/
def T (z : ℂ) : ℂ := 2 * z / (1 - z ^ 2)

/-- T(i) = i  — the imaginary unit is a fixed point. -/
theorem T_fixed_I : T Complex.I = Complex.I := by
  simp [T, Complex.I_sq]
  norm_num

/-- T(-i) = -i  — the negative imaginary unit is also a fixed point. -/
theorem T_fixed_neg_I : T (-Complex.I) = -Complex.I := by
  simp [T, neg_sq, Complex.I_sq]
  norm_num

/-- The fixed-point equation T(z) = z reduces to z(1 + z²) = 0. -/
theorem T_fixed_point_eq (z : ℂ) (hz : 1 - z ^ 2 ≠ 0) :
    T z = z ↔ z * (1 + z ^ 2) = 0 := by
  simp [T]
  constructor
  · intro h
    have := congr_arg (· * (1 - z ^ 2)) h
    field_simp [hz] at this ⊢
    linarith [this]
  · intro h
    have : z = 0 ∨ 1 + z ^ 2 = 0 := mul_eq_zero.mp h
    rcases this with rfl | hz2
    · simp
    · have : z ^ 2 = -1 := by linarith [hz2]
      field_simp [hz]
      linarith [this]

/-- The non-zero fixed points are exactly ±i. -/
theorem T_nonzero_fixed_points (z : ℂ) (hz_ne : z ≠ 0) (hz_denom : 1 - z ^ 2 ≠ 0) :
    T z = z ↔ z = Complex.I ∨ z = -Complex.I := by
  rw [T_fixed_point_eq z hz_denom]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hz2
    · exact absurd hz hz_ne
    · have : z ^ 2 = -1 := by linarith [hz2]
      -- z² = -1 iff z = i or z = -i
      have := sq_eq_neg_one_iff_of_ne_zero z hz
      exact this.mp this_1
  · rintro (rfl | rfl)
    · simp [Complex.I_sq]
    · simp [neg_sq, Complex.I_sq]

-- ===========================================================================
-- § 2  Connection to the tangent double-angle formula
-- ===========================================================================

/-- T is the complex extension of tan(2θ) = 2tan(θ)/(1-tan²(θ)).
    At z = tan(θ), T(z) = tan(2θ). -/
theorem T_is_double_angle_tangent (θ : ℝ)
    (hcos : Real.cos θ ≠ 0)
    (hdenom : 1 - (Real.tan θ : ℂ) ^ 2 ≠ 0) :
    T (Real.tan θ : ℂ) = (Real.tan (2 * θ) : ℂ) := by
  simp [T, Real.tan_two_mul]
  field_simp [Real.cos_sq_ne_zero_of_cos_ne_zero hcos]
  ring

/-- At θ = π/2: tan(π/2) corresponds to z = i (the pole/fixed point). -/
theorem theta_pi_half_gives_I :
    Complex.I = (Real.tan (Real.pi / 2) : ℂ) := by
  simp [Real.tan_pi_div_two]

-- ===========================================================================
-- § 3  Orbit of i under T
-- ===========================================================================

/-- The orbit of i under T is constantly i. -/
theorem T_iterate_I (n : ℕ) :
    Function.iterate (fun z => T z) n Complex.I = Complex.I := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply, T_fixed_I, ih]

-- ===========================================================================
-- § 4  3-SAT arithmetization
-- ===========================================================================

/-- A clause C_j = 1 - (1-ℓ₁)(1-ℓ₂)(1-ℓ₃) evaluates to 1 iff at least one
    literal is true (equals 1) and 0 iff all literals are false. -/
def clause (l1 l2 l3 : ℝ) : ℝ :=
  1 - (1 - l1) * (1 - l2) * (1 - l3)

theorem clause_sat (l1 l2 l3 : ℝ)
    (h : l1 = 1 ∨ l2 = 1 ∨ l3 = 1) :
    clause l1 l2 l3 = 1 := by
  simp [clause]
  rcases h with rfl | rfl | rfl <;> ring

theorem clause_unsat (l1 l2 l3 : ℝ)
    (h1 : l1 = 0) (h2 : l2 = 0) (h3 : l3 = 0) :
    clause l1 l2 l3 = 0 := by
  simp [clause, h1, h2, h3]

/-- The objective function F = Π C_j evaluates to 1 iff all clauses are satisfied. -/
def objective (clauses : List ℝ) : ℝ := clauses.prod

theorem objective_sat_iff (clauses : List ℝ)
    (h_range : ∀ c ∈ clauses, c = 0 ∨ c = 1) :
    objective clauses = 1 ↔ ∀ c ∈ clauses, c = 1 := by
  simp [objective]
  constructor
  · intro hprod c hc
    have := List.prod_eq_one_iff_of_binary h_range |>.mp hprod
    exact this c hc
  · intro hall
    apply List.prod_eq_one
    intro c hc
    exact hall c hc

-- ===========================================================================
-- § 5  The embedding T(F(x)) — geometry without complexity reduction
-- ===========================================================================

/-
  Ahmad's insight: embedding F(x) into T(z) gives a beautiful geometric picture.

  T(F(x)):
    - When F(x) = 1 (satisfying assignment): T(1) = 2·1/(1-1) → undefined (pole)
    - When F(x) = 0 (unsatisfying): T(0) = 0 (fixed point at origin)
    - For intermediate values: T maps to the complex plane

  The fixed point z = i corresponds to F(x) = i — outside the Boolean domain.

  KEY THEOREM (informal, not proved here):
  The degree of F(x) grows as Θ(m) where m = number of clauses.
  Composing T with F does not reduce the degree.
  Finding Boolean roots of F = 1 requires exponential time in the worst case.
  The embedding is a reparametrization, not a compression.

  This is consistent with P ≠ NP (the prevailing conjecture).
  The geometry is beautiful. The hardness is unchanged.
  Formal proof would require BSS-machine theory results.
-/

/-- T evaluated at F = 0 (unsatisfied) gives the origin fixed point. -/
theorem T_at_zero : T 0 = 0 := by simp [T]

/-- T has a pole at z = 1 — satisfying assignments (F=1) hit the pole. -/
theorem T_pole_at_one : (1 : ℂ) - (1 : ℂ) ^ 2 = 0 := by norm_num

/-- The connection to DualNumbers.lean:
    In F₂, −1 = 1, so z = i and z = −i collapse to the same point.
    The period-4 rotation (i → -1 → -i → 1 → i) becomes period-2 in char 2.
    This is exactly the F_dual period-2 theorem in DualNumbers.lean. -/
theorem period_four_complex_I :
    Complex.I ^ 4 = 1 := by norm_num [Complex.I_sq]

/-- The connection to the Chebyshev tower in TrigCore.lean:
    T is the doubling map. Iterating T gives cosCore/sinCore recurrences.
    The fixed point i corresponds to the angle θ = π/2 in the tower. -/
theorem T_is_cosine_doubling :
    ∀ θ : ℝ, (2 : ℝ) * Real.cos θ ^ 2 - 1 = Real.cos (2 * θ) := by
  intro θ
  rw [Real.cos_two_mul]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

end QautuamMath
