/-
  Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.

  ComplexCore.lean — Complex Analysis Formalization for Q-Autuam
  ==============================================================
  A library of Lean 4 (Mathlib) theorems underlying the complexCore and trigCore
  operators in Q-Autuam. Builds from the 2×2 real matrix representation of ℂ
  through polar decomposition to the branch-controlled complex logarithm.

  Module structure:
  § 1  Real matrix representation of complex multiplication
  § 2  Determinant = normSq correspondence
  § 3  Determinant multiplicativity
  § 4  normSq_mul via component expansion (ring proof)
  § 5  Euler identity — exp(iθ) = cos θ + i sin θ
  § 6  Polar decomposition — z = |z| · phase(arg z)
  § 7  Argument multiplicativity mod 2π
  § 8  Principal logarithm definition and power law
  § 9  Principal log of positive reals
  § 10 Log product rule mod 2π
  § 11 Log division rule mod 2π
  § 12 Branch-controlled region (integer witness = 0)

  References:
  [1]  Geometric interpretation of det of complex matrix
       https://math.stackexchange.com/questions/1727571/geometric-interpretation-of-the-determinant-of-a-complex-matrix
  [2]  Determinant — Wikipedia https://en.wikipedia.org/wiki/Determinant
  [3]  Properties of Determinants
       https://math.libretexts.org/Bookshelves/Linear_Algebra/A_First_Course_in_Linear_Algebra_(Kuttler)/03:_Determinants/3.02:_Properties_of_Determinants
  [4]  Complex number — Wikipedia https://en.wikipedia.org/wiki/Complex_number
  [5]  Euler's formula — Wikipedia https://en.wikipedia.org/wiki/Euler's_formula
  [6]  Euler's formula — YouTube https://www.youtube.com/watch?v=CpKD9aYEdms
  [7]  Proofs of trig identities
       https://en.wikipedia.org/wiki/Proofs_of_trigonometric_identities
  [8]  Deriving Sum/Difference Identities — YouTube
       https://www.youtube.com/watch?v=XfS5UZQca0g
  [9]  Complex logarithm — Wikipedia https://wikipedia.org/wiki/Complex_logarithm
  [10] Properties of Complex Logarithms — YouTube
       https://www.youtube.com/watch?v=sria1o3p6YY
  [11] Mathlib.Data.Complex.Basic
       https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html
  [12] Complex Analysis L04 — YouTube https://www.youtube.com/watch?v=CpKD9aYEdms
  [13] Proof of Euler's Identity — YouTube https://www.youtube.com/watch?v=HKWBAgU7ISk
  [14] Khan Academy — Pythagorean trig identity
       https://www.khanacademy.org/math/trigonometry/unit-circle-trig-func/pythagorean-identity/v/using-the-pythagorean-trig-identity
  [15] Multiplicativity of the Determinant https://androma.org/theorems/10870
  [16] Intuitive Arithmetic With Complex Numbers
       https://betterexplained.com/articles/intuitive-arithmetic-with-complex-numbers/
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Tactic

noncomputable section
open Real Complex Matrix

namespace QautuamMath

abbrev Fin2 := Fin 2

-- ===========================================================================
-- § 1  Real 2×2 matrix representation of ℂ
-- ===========================================================================

/-- The standard realification: z ↦ [[Re z, -Im z], [Im z, Re z]]. -/
def complexToMat (z : ℂ) : Matrix Fin2 Fin2 ℝ :=
  !![z.re, -z.im; z.im, z.re]

/-- complexToMat respects complex multiplication. -/
theorem complexToMat_mul (z w : ℂ) :
    complexToMat (z * w) = complexToMat z * complexToMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexToMat, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]
  all_goals ring

-- ===========================================================================
-- § 2  Determinant = normSq correspondence
-- ===========================================================================

/-- det(complexToMat z) = ‖z‖² (realification preserves the squared norm). -/
theorem det_complexToMat (z : ℂ) :
    Matrix.det (complexToMat z) = Complex.normSq z := by
  rw [Matrix.det_fin_two]
  simp [complexToMat, Complex.normSq_apply]
  ring

/-- Explicit form without normSq. -/
theorem det_complexToMat' (z : ℂ) :
    Matrix.det (complexToMat z) = z.re ^ 2 + z.im ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [complexToMat]; ring

-- ===========================================================================
-- § 3  Determinant multiplicativity
-- ===========================================================================

/-- det is multiplicative: det(complexToMat(zw)) = det(complexToMat z)·det(complexToMat w). -/
theorem det_complexToMat_mul (z w : ℂ) :
    Matrix.det (complexToMat (z * w)) =
      Matrix.det (complexToMat z) * Matrix.det (complexToMat w) := by
  rw [complexToMat_mul]
  exact Matrix.det_mul _ _

/-- normSq is multiplicative (via determinant route). -/
theorem normSq_mul_via_complexToMat (z w : ℂ) :
    Complex.normSq (z * w) =
      Complex.normSq z * Complex.normSq w := by
  rw [← det_complexToMat, det_complexToMat_mul, det_complexToMat, det_complexToMat]

/-- det of the n-th power. -/
theorem det_complexToMat_pow (z : ℂ) (n : ℕ) :
    Matrix.det (complexToMat (z ^ n)) =
      (Matrix.det (complexToMat z)) ^ n := by
  induction n with
  | zero => simp [complexToMat]
  | succ n ih =>
      rw [pow_succ, complexToMat_mul, Matrix.det_mul, ih]
      ring

-- ===========================================================================
-- § 4  normSq_mul via component expansion (ring proof)
-- ===========================================================================

/-- Direct proof that ‖zw‖² = ‖z‖²·‖w‖² via component arithmetic. -/
theorem normSq_mul_components (z w : ℂ) :
    Complex.normSq (z * w) =
      Complex.normSq z * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

-- ===========================================================================
-- § 5  Euler identity
-- ===========================================================================

/-- The unit phase: cos θ + i sin θ. -/
def phase (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)

theorem phase_re (θ : ℝ) : (phase θ).re = Real.cos θ := by simp [phase]
theorem phase_im (θ : ℝ) : (phase θ).im = Real.sin θ := by simp [phase]

/-- exp(iθ) = cos θ + i sin θ. -/
theorem exp_I_mul_eq_phase (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) = phase θ := by
  apply Complex.ext
  · simp [phase, Complex.exp_mul_I]
  · simp [phase, Complex.exp_mul_I]

/-- normSq of the phase is 1 (unit circle). -/
theorem normSq_phase (θ : ℝ) : Complex.normSq (phase θ) = 1 := by
  simp [phase, Complex.normSq_apply]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- det of the matrix image of a phase is 1. -/
theorem det_complexToMat_phase (θ : ℝ) :
    Matrix.det (complexToMat (phase θ)) = 1 := by
  rw [det_complexToMat, normSq_phase]

/-- General polar exponential: exp(a + ib) = e^a · (cos b + i sin b). -/
theorem exp_components (a b : ℝ) :
    Complex.exp ((a : ℂ) + Complex.I * (b : ℂ)) =
      (Real.exp a : ℂ) * ((Real.cos b : ℂ) + Complex.I * (Real.sin b : ℂ)) := by
  apply Complex.ext <;> simp [Complex.exp_add, exp_I_mul_eq_phase, phase] <;> ring

-- ===========================================================================
-- § 6  Polar decomposition
-- ===========================================================================

/-- Polar reconstruction: |z| · phase(arg z). -/
def polarReconstruct (z : ℂ) : ℂ :=
  (Complex.abs z : ℂ) * phase (Complex.arg z)

theorem abs_sq_eq_normSq (z : ℂ) :
    Complex.abs z ^ 2 = Complex.normSq z := by
  simpa using Complex.sq_abs z

theorem polarPhase_re (θ : ℝ) : (phase θ).re = Real.cos θ := phase_re θ
theorem polarPhase_im (θ : ℝ) : (phase θ).im = Real.sin θ := phase_im θ

/-- Polar decomposition: z = |z| · (cos(arg z) + i·sin(arg z)). -/
theorem polar_decomposition (z : ℂ) :
    z = (Complex.abs z : ℂ) *
          ((Real.cos (Complex.arg z) : ℂ) +
           Complex.I * (Real.sin (Complex.arg z) : ℂ)) := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.cos_arg]
  · simp [Complex.mul_im, Complex.sin_arg]

theorem polar_decomposition_phase (z : ℂ) :
    z = (Complex.abs z : ℂ) * phase (Complex.arg z) := by
  simpa [phase] using polar_decomposition z

/-- Unit phase of z (normalized to lie on S¹). -/
def unitPhase (z : ℂ) : ℂ := z / (Complex.abs z : ℂ)

theorem unitPhase_eq_phase (z : ℂ) (hz : z ≠ 0) :
    unitPhase z = phase (Complex.arg z) := by
  unfold unitPhase
  rw [polar_decomposition_phase z]
  field_simp [hz]

-- ===========================================================================
-- § 7  Argument multiplicativity mod 2π
-- ===========================================================================

/-- arg(z·w) ≡ arg z + arg w (mod 2π). -/
theorem arg_mul_mod_two_pi (z w : ℂ) :
    Complex.arg (z * w) ≡
      Complex.arg z + Complex.arg w [MOD (2 * Real.pi)] := by
  simpa [mul_comm] using Complex.arg_mul z w

theorem arg_mul_mod_two_pi_ne_zero (z w : ℂ) (_ : z ≠ 0) (_ : w ≠ 0) :
    Complex.arg (z * w) ≡
      Complex.arg z + Complex.arg w [MOD (2 * Real.pi)] :=
  arg_mul_mod_two_pi z w

/-- Existential integer-witness form of arg multiplicativity. -/
theorem arg_mul_exists_turns (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ∃ k : ℤ,
      Complex.arg (z * w) =
        Complex.arg z + Complex.arg w + (k : ℝ) * (2 * Real.pi) := by
  rcases arg_mul_mod_two_pi_ne_zero z w hz hw with ⟨k, hk⟩
  exact ⟨k, by linarith⟩

/-- arg(z^n) ≡ n·arg z (mod 2π). -/
theorem arg_pow_mod_two_pi (z : ℂ) : ∀ n : ℕ,
    Complex.arg (z ^ n) ≡
      (n : ℝ) * Complex.arg z [MOD (2 * Real.pi)] := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.arg_mul]
      convert ih.add_right (Complex.arg z) using 1
      push_cast; ring

-- ===========================================================================
-- § 8  Principal logarithm definition and power law
-- ===========================================================================

/-- Principal logarithm in polar-coordinate form. -/
def principalLog (z : ℂ) : ℂ :=
  (Real.log (Complex.abs z) : ℂ) + Complex.I * (Complex.arg z : ℂ)

@[simp] theorem principalLog_im (z : ℂ) :
    (principalLog z).im = Complex.arg z := by
  simp [principalLog]

/-- The complexCore: phase θ raised to the n-th power. -/
def complexCore (θ : ℝ) (n : ℕ) : ℂ := phase θ ^ n

theorem det_complexToMat_complexCore (θ : ℝ) (n : ℕ) :
    Matrix.det (complexToMat (complexCore θ n)) = 1 := by
  unfold complexCore
  rw [det_complexToMat_pow, det_complexToMat_phase, one_pow]

/-- Imaginary part of principalLog(z^n) satisfies the power mod 2π law. -/
theorem principalLog_pow_im_mod_two_pi (z : ℂ) (n : ℕ) :
    (principalLog (z ^ n)).im ≡
      (n : ℝ) * (principalLog z).im [MOD (2 * Real.pi)] := by
  simpa [principalLog] using arg_pow_mod_two_pi z n

-- ===========================================================================
-- § 9  Principal log of positive reals
-- ===========================================================================

/-- For x > 0, the principal logarithm is purely real: principalLog x = log x. -/
theorem principalLog_of_real_pos (x : ℝ) (hx : 0 < x) :
    principalLog (x : ℂ) = (Real.log x : ℂ) := by
  unfold principalLog
  have habs : Complex.abs (x : ℂ) = x := by
    rw [Complex.abs_ofReal]; exact abs_of_pos hx
  have harg : Complex.arg (x : ℂ) = 0 :=
    Complex.arg_ofReal_pos hx
  rw [habs, harg]; simp

theorem principalLog_of_real_pos_re (x : ℝ) (hx : 0 < x) :
    (principalLog (x : ℂ)).re = Real.log x := by
  rw [principalLog_of_real_pos x hx]; simp

theorem principalLog_of_real_pos_im (x : ℝ) (hx : 0 < x) :
    (principalLog (x : ℂ)).im = 0 := by
  rw [principalLog_of_real_pos x hx]; simp

theorem exp_principalLog_of_real_pos (x : ℝ) (hx : 0 < x) :
    Complex.exp (principalLog (x : ℂ)) = (x : ℂ) := by
  rw [principalLog_of_real_pos x hx]
  simp [Real.exp_log hx]

-- ===========================================================================
-- § 10  Log product rule mod 2π
-- ===========================================================================

/-- Real part of principalLog(zw) = real parts add (exact). -/
theorem principalLog_mul_re (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    (principalLog (z * w)).re = (principalLog z).re + (principalLog w).re := by
  simp only [principalLog, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.abs.map_mul, Real.log_mul
        (Complex.abs_pos.mpr hz) (Complex.abs_pos.mpr hw)]

/-- Imaginary part of principalLog(zw) ≡ sum of imaginary parts (mod 2π). -/
theorem principalLog_mul_im_mod_two_pi (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    (principalLog (z * w)).im ≡
      (principalLog z).im + (principalLog w).im [MOD (2 * Real.pi)] := by
  simp only [principalLog, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    zero_mul, one_mul, add_zero]
  simpa using arg_mul_mod_two_pi_ne_zero z w hz hw

/-- Full complex log product rule: ∃ k, principalLog(zw) = principalLog z + principalLog w + 2πki. -/
theorem principalLog_mul_exists_turn (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ∃ k : ℤ,
      principalLog (z * w) =
        principalLog z + principalLog w +
          Complex.I * ((2 * Real.pi * (k : ℝ)) : ℂ) := by
  have hre := principalLog_mul_re z w hz hw
  have him := principalLog_mul_im_mod_two_pi z w hz hw
  rcases him with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero]
    exact hre
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero]
    linarith

-- ===========================================================================
-- § 11  Log division rule mod 2π
-- ===========================================================================

/-- arg(w⁻¹) ≡ -arg w (mod 2π). -/
theorem arg_inv_mod_two_pi (w : ℂ) :
    Complex.arg w⁻¹ ≡ -Complex.arg w [MOD (2 * Real.pi)] := by
  simpa using Complex.arg_inv w

/-- arg(z/w) ≡ arg z - arg w (mod 2π). -/
theorem arg_div_mod_two_pi (z w : ℂ) :
    Complex.arg (z / w) ≡
      Complex.arg z - Complex.arg w [MOD (2 * Real.pi)] := by
  rw [div_eq_mul_inv]
  calc Complex.arg (z * w⁻¹)
      ≡ Complex.arg z + Complex.arg w⁻¹ [MOD (2 * Real.pi)] :=
          Complex.arg_mul z w⁻¹
    _ ≡ Complex.arg z + (-Complex.arg w) [MOD (2 * Real.pi)] :=
          Int.ModEq.add_left _ (arg_inv_mod_two_pi w)
    _ = Complex.arg z - Complex.arg w := by ring

/-- Real part of principalLog(z/w) = difference of real parts (exact). -/
theorem principalLog_div_re (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    (principalLog (z / w)).re = (principalLog z).re - (principalLog w).re := by
  simp only [principalLog, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show (z / w) = z * w⁻¹ from div_eq_mul_inv z w]
  rw [Complex.abs.map_mul, Complex.abs.map_inv,
      Real.log_mul (Complex.abs_pos.mpr hz)
        (by simp [Complex.abs_pos.mpr hw]),
      Real.log_inv]

/-- Full complex log division rule: ∃ k, principalLog(z/w) = principalLog z - principalLog w + 2πki. -/
theorem principalLog_div_exists_turn (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ∃ k : ℤ,
      principalLog (z / w) =
        principalLog z - principalLog w +
          Complex.I * ((2 * Real.pi * (k : ℝ)) : ℂ) := by
  have hre := principalLog_div_re z w hz hw
  have him := arg_div_mod_two_pi z w
  rcases him with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply Complex.ext
  · simp only [principalLog, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    exact hre
  · simp only [principalLog, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_mul, one_mul, add_zero]
    linarith

-- ===========================================================================
-- § 12  Branch-controlled region (integer witness = 0)
-- ===========================================================================

/-- A real value lies in the principal argument range (-π, π]. -/
def InPrincipalArgRange (x : ℝ) : Prop :=
  -Real.pi < x ∧ x ≤ Real.pi

/-- An integer turn that keeps a value in (-π, π] must be zero. -/
lemma int_turn_eq_zero_of_principal_range
    (a : ℝ) (k : ℤ)
    (ha  : InPrincipalArgRange a)
    (hak : InPrincipalArgRange (a + (2 * Real.pi) * (k : ℝ))) :
    k = 0 := by
  rcases ha  with ⟨ha_lo,  ha_hi⟩
  rcases hak with ⟨hak_lo, hak_hi⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  by_contra hk
  rcases Int.lt_or_gt_of_ne hk with hk_neg | hk_pos
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
    linarith [show a + (2 * Real.pi) * (k : ℝ) < -Real.pi by nlinarith]
  · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hk_pos
    linarith [show Real.pi < a + (2 * Real.pi) * (k : ℝ) by nlinarith]

/-- When the argument difference lies in the principal branch, the integer witness is 0. -/
theorem arg_div_witness_zero_of_sub_in_principal_range
    (z w : ℂ) (k : ℤ)
    (_ : w ≠ 0)
    (hk   : Complex.arg (z / w) =
              Complex.arg z - Complex.arg w + (2 * Real.pi) * (k : ℝ))
    (hsum : InPrincipalArgRange (Complex.arg z - Complex.arg w)) :
    k = 0 := by
  have hdiv_range : InPrincipalArgRange (Complex.arg (z / w)) :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  rw [hk] at hdiv_range
  exact int_turn_eq_zero_of_principal_range
    (Complex.arg z - Complex.arg w) k hsum hdiv_range

/-- Branch-controlled log division: if arg z - arg w ∈ (-π, π], then principalLog(z/w) = principalLog z - principalLog w. -/
theorem principalLog_div_eq_of_branch_control
    (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0)
    (hsum : InPrincipalArgRange (Complex.arg z - Complex.arg w)) :
    principalLog (z / w) = principalLog z - principalLog w := by
  rcases principalLog_div_exists_turn z w hz hw with ⟨k, hk⟩
  have hk0 : k = 0 := by
    apply arg_div_witness_zero_of_sub_in_principal_range z w k hw _ hsum
    -- Extract arg witness from imaginary parts of hk
    have him := congr_arg Complex.im hk
    simp only [principalLog, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_mul, one_mul, add_zero] at him
    linarith
  simp [hk0] at hk
  linarith [hk]  -- both sides equal after k=0 substitution

end QautuamMath
