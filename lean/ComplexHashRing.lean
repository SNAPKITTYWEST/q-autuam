/-
  Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.

  ComplexHashRing.lean — Imaginary Hash, Equiv, CommRing, Scalar Embedding
  =========================================================================
  Zero-sorry Lean 4 proofs:

  § 1  Trivial imaginary-value hash: H(x) = (0, x)
       - Pre-image search is O(n) — in P, not NP-hard
       - imagProjection ∘ hash = id  (surjectivity onto pure-imaginary subtype)

  § 2  F_dual as involution (period 2) and full iteration properties

  § 3  fullHash bijectivity as an Equiv
       - fullHashEquiv : BitVec n × BitVec n ≃ MyComplex n

  § 4  MyComplex R as a CommRing (complex multiplication over any comm ring R)
       - I² = -1
       - negImagFunctor period 4 in general, period 2 in ZMod 2

  § 5  Scalar embedding R →+* MyComplex R

  References:
  [1]  Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean/
  [2]  Hitchhiker's guide to Lean 4 theorems
       https://blog.lambdaclass.com/the-hitchhikers-guide-to-reading-lean-4-theorems/
  [3]  Hash function — Wikipedia https://en.wikipedia.org/wiki/Hash_function
  [4]  Dual number — Wikipedia https://en.wikipedia.org/wiki/Dual_number
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace QautuamMath

-- ===========================================================================
-- § 1  Imaginary-value hash and preimage structure
-- ===========================================================================

/-- A complex number as a pair of n-bit vectors. -/
structure MyComplex (n : ℕ) where
  re : BitVec n
  im : BitVec n
  deriving DecidableEq, Repr

/-- Trivial hash: H(x) = (0, x).
    Real part is always zero; imaginary part is the entire input.
    This is NOT a cryptographic hash — it is invertible in O(n). -/
def hash {n : ℕ} (x : BitVec n) : MyComplex n := ⟨0, x⟩

/-- The imaginary projection. -/
def imagProjection {n : ℕ} (z : MyComplex n) : BitVec n := z.im

/-- imagProjection ∘ hash = id  (the key invariant). -/
@[simp] theorem hash_im {n : ℕ} (x : BitVec n) : (hash x).im = x := rfl

/-- The imaginary invariant: ImagInvariant x ↔ (hash x).im = x. -/
def ImagInvariant {n : ℕ} (x : BitVec n) : Prop := (hash x).im = x

theorem hash_preserves_imaginary_invariant {n : ℕ} (x : BitVec n) :
    ImagInvariant x := rfl

/-- A target y has an imaginary preimage iff ∃ x, (hash x).im = y. -/
def HasImaginaryPreimage {n : ℕ} (y : BitVec n) : Prop :=
  ∃ x : BitVec n, (hash x).im = y

/-- Every target has itself as the canonical preimage (O(n) copy). -/
def findPreimage {n : ℕ} (y : BitVec n) : BitVec n := y

theorem findPreimage_correct {n : ℕ} (y : BitVec n) :
    (hash (findPreimage y)).im = y := rfl

theorem every_target_has_imaginary_preimage {n : ℕ} (y : BitVec n) :
    HasImaginaryPreimage y := ⟨y, rfl⟩

/-- imagProjection ∘ hash is surjective — every n-bit value is a valid output. -/
theorem imagProjection_hash_surjective (n : ℕ) :
    Function.Surjective (fun x : BitVec n => imagProjection (hash x)) := by
  intro y; exact ⟨y, rfl⟩

/-- The decision problem "∃ x, imag(H(x)) = y" is always true (trivially in P). -/
theorem imaginary_preimage_iff_true {n : ℕ} (y : BitVec n) :
    HasImaginaryPreimage y ↔ True := by
  simp [every_target_has_imaginary_preimage]

/-- Linear cost bound: copying n bits costs n units. -/
def preimageCost (n : ℕ) : ℕ := n

def IsLinearBound (cost : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, cost n ≤ c * n + c

theorem findPreimage_linear_bound : IsLinearBound preimageCost := by
  refine ⟨1, ?_⟩; intro n; simp [preimageCost]; omega

-- ===========================================================================
-- § 2  F_dual involution (period 2 in 𝔽₂)
-- ===========================================================================

abbrev F2 := ZMod 2

structure DualF2 where
  primal  : F2
  tangent : F2
  deriving DecidableEq, Repr

/-- F_dual swaps primal and tangent. Over 𝔽₂, -1=1 so period is 2 (not 4). -/
def F_dual (x : DualF2) : DualF2 := ⟨x.tangent, x.primal⟩

/-- F_dual is an involution: applying it twice is identity. -/
theorem F_dual_apply_twice (x : DualF2) : F_dual (F_dual x) = x := by
  cases x; rfl

/-- F_dual is involutive. -/
theorem F_dual_is_involution : Function.Involutive F_dual :=
  fun x => F_dual_apply_twice x

/-- Period 2 via Function.iterate. -/
theorem F_dual_iterate_two (x : DualF2) :
    Function.iterate 2 F_dual x = x := by
  simp [Function.iterate_succ_apply, F_dual]

/-- All even iterations are identity. -/
theorem F_dual_iterate_even (n : ℕ) (x : DualF2) :
    Function.iterate (2 * n) F_dual x = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ]
      change Function.iterate (2 * n) F_dual (F_dual (F_dual x)) = x
      rw [F_dual_apply_twice]; exact ih x

/-- All odd iterations equal a single application. -/
theorem F_dual_iterate_odd (n : ℕ) (x : DualF2) :
    Function.iterate (2 * n + 1) F_dual x = F_dual x := by
  rw [Function.iterate_add_apply, F_dual_iterate_even]
  simp [Function.iterate_one]

-- ===========================================================================
-- § 3  fullHash bijectivity as an Equiv
-- ===========================================================================

/-- fullHash encodes a pair of bit-vectors as a MyComplex. -/
def fullHash {n : ℕ} (x : BitVec n × BitVec n) : MyComplex n := ⟨x.1, x.2⟩

/-- fullPreimage extracts the coordinate pair. -/
def fullPreimage {n : ℕ} (z : MyComplex n) : BitVec n × BitVec n := (z.re, z.im)

@[simp] theorem fullPreimage_fullHash {n : ℕ} (x : BitVec n × BitVec n) :
    fullPreimage (fullHash x) = x := by cases x; rfl

@[simp] theorem fullHash_fullPreimage {n : ℕ} (z : MyComplex n) :
    fullHash (fullPreimage z) = z := by cases z; rfl

/-- fullHash is a bijection — an Equiv between pairs and MyComplex. -/
def fullHashEquiv (n : ℕ) : BitVec n × BitVec n ≃ MyComplex n where
  toFun    := fullHash
  invFun   := fullPreimage
  left_inv := by intro x; cases x; rfl
  right_inv := by intro z; cases z; rfl

@[simp] theorem fullHashEquiv_symm_apply {n : ℕ} (z : MyComplex n) :
    (fullHashEquiv n).symm z = (z.re, z.im) := rfl

@[simp] theorem fullHashEquiv_symm_re {n : ℕ} (z : MyComplex n) :
    ((fullHashEquiv n).symm z).1 = z.re := rfl

@[simp] theorem fullHashEquiv_symm_im {n : ℕ} (z : MyComplex n) :
    ((fullHashEquiv n).symm z).2 = z.im := rfl

theorem fullHash_injective  (n : ℕ) : Function.Injective  (@fullHash n) :=
  (fullHashEquiv n).injective

theorem fullHash_surjective  (n : ℕ) : Function.Surjective (@fullHash n) :=
  (fullHashEquiv n).surjective

theorem fullHash_bijective   (n : ℕ) : Function.Bijective  (@fullHash n) :=
  (fullHashEquiv n).bijective

-- ===========================================================================
-- § 4  MyComplex R as a CommRing (generic over any comm ring R)
-- ===========================================================================

namespace MyComplexR

variable {R : Type*} [CommRing R]

/-- Generic complex pair over a commutative ring R. -/
structure MyComplexR (R : Type*) where
  re : R
  im : R
  deriving DecidableEq, Repr

instance : Zero (MyComplexR R) where zero := ⟨0, 0⟩
instance : One  (MyComplexR R) where one  := ⟨1, 0⟩

instance : Add (MyComplexR R) where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

instance : Neg (MyComplexR R) where
  neg x := ⟨-x.re, -x.im⟩

instance : Sub (MyComplexR R) where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

/-- Complex multiplication: (a+bi)(c+di) = (ac-bd) + (ad+bc)i. -/
instance : Mul (MyComplexR R) where
  mul x y := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

@[ext]
theorem ext {x y : MyComplexR R} (hre : x.re = y.re) (him : x.im = y.im) :
    x = y := by cases x; cases y; cases hre; cases him; rfl

@[simp] theorem add_re (x y : MyComplexR R) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : MyComplexR R) : (x + y).im = x.im + y.im := rfl
@[simp] theorem mul_re (x y : MyComplexR R) :
    (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : MyComplexR R) :
    (x * y).im = x.re * y.im + x.im * y.re := rfl

instance : CommRing (MyComplexR R) where
  add_assoc   x y z := by ext <;> simp [add_assoc]
  zero_add    x     := by ext <;> simp
  add_zero    x     := by ext <;> simp
  add_comm    x y   := by ext <;> simp [add_comm]
  neg_add_cancel x  := by ext <;> simp
  sub_eq_add_neg x y := by ext <;> simp [sub_eq_add_neg]
  mul_assoc   x y z := by ext <;> simp only [mul_re, mul_im] <;> ring
  one_mul     x     := by ext <;> simp
  mul_one     x     := by ext <;> simp
  left_distrib  x y z := by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  right_distrib x y z := by ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring
  mul_comm    x y   := by ext <;> simp only [mul_re, mul_im] <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The imaginary unit: I² = -1. -/
def I : MyComplexR R := ⟨0, 1⟩

theorem I_sq : I * I = (-1 : MyComplexR R) := by ext <;> simp [I]

/-- Clockwise phase functor: F(z) = -i·z = (im z, -re z). -/
def negImagFunctor (z : MyComplexR R) : MyComplexR R := (-I) * z

theorem negImagFunctor_apply (z : MyComplexR R) :
    negImagFunctor z = ⟨z.im, -z.re⟩ := by ext <;> simp [negImagFunctor, I]

/-- Period 4 in general ((-i)⁴ = 1 when -1 ≠ 1). -/
theorem negImagFunctor_four (z : MyComplexR R) :
    negImagFunctor (negImagFunctor (negImagFunctor (negImagFunctor z))) = z := by
  simp [negImagFunctor, I]; ring

/-- Period 2 in ZMod 2 (because -1 = 1 there). -/
theorem negImagFunctor_charTwo (z : MyComplexR (ZMod 2)) :
    negImagFunctor (negImagFunctor z) = z := by
  ext <;> simp [negImagFunctor, I]

-- ===========================================================================
-- § 5  Scalar embedding R →+* MyComplexR R
-- ===========================================================================

/-- Embed a scalar r as (r, 0). -/
def scalarEmbed (r : R) : MyComplexR R := ⟨r, 0⟩

/-- The scalar embedding is a ring homomorphism. -/
def scalarEmbedRingHom : R →+* MyComplexR R where
  toFun    := scalarEmbed
  map_zero' := rfl
  map_one'  := rfl
  map_add'  := by intro a b; ext <;> simp [scalarEmbed]
  map_mul'  := by intro a b; ext <;> simp [scalarEmbed]

@[simp] theorem scalarEmbed_re (r : R) : (scalarEmbed r).re = r := rfl
@[simp] theorem scalarEmbed_im (r : R) : (scalarEmbed r).im = 0 := rfl

theorem scalarEmbed_injective : Function.Injective (@scalarEmbed R _) := by
  intro a b h; exact congrArg MyComplexR.re h

end MyComplexR

end QautuamMath
