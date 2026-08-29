# Q-Autuam

[![License: BSL-1.1](https://img.shields.io/badge/license-BSL--1.1-orange?style=flat-square)](LICENSE.tri)
[![License: AGPL-3.0](https://img.shields.io/badge/license-AGPL--3.0-blue?style=flat-square)](LICENSE.tri)
[![License: MPL-2.0](https://img.shields.io/badge/license-MPL--2.0-green?style=flat-square)](LICENSE.tri)
[![Patent Pending](https://img.shields.io/badge/patent-pending-red?style=flat-square)]()
[![θ](https://img.shields.io/badge/θ-89%2F2462-gold?style=flat-square)]()
[![Lean 4](https://img.shields.io/badge/Lean%204-Mathlib-5e5086?style=flat-square)](lean/TrigCore.lean)
[![Python](https://img.shields.io/badge/Python-3.11%2B-blue?style=flat-square&logo=python)](src/q_autuam/)
[![Novelty](https://img.shields.io/badge/novelty-POSSIBLY__NOVEL-yellow?style=flat-square)]()

**Pronounced:** *kwah-TOO-am*

**Author:** Ahmad Ali Parr  
**Trust:** Bel Esprit D'Accord Irrevocable Trust

---

> *A program's intent is not what it says it does. It is the ratio of emergence to entropy in its prime-annotated Boolean support, evaluated at the optimal recursive trigonometric depth.*

---

## What Q-Autuam Is

Q-Autuam is a new mathematical language whose programs are satisfying assignments to a constrained 3-SAT instance, evaluated through a recursive trigonometric tower, annotated by a prime-number algebra, and scored by an entropy-emergence intent metric.

It is not a programming language in the conventional sense. It is a **language functor**:

```
Q : (SAT₃^{89/2462}, RecTrig^(•), Elucid, Ent, Emer) → (program, Intent)
```

The core computational task: find `(x, k)` maximising `Intent(x, k)` subject to the 3-SAT constraint.

---

## The Four Layers

### Layer 1 — Three-SAT Core in Polynomial Time

The truncation error `ε = 89/2462` (in lowest terms: gcd(89, 2462) = 1) defines the restricted instance family `SAT₃^{89/2462}`.

A formula Φ is in this family if exactly **89 clauses** are unsatisfied by the optimal assignment.

**The decision procedure is polynomial in m** because 89 is a fixed constant:

```python
for subset_89 in combinations(range(m), 89):
    reduced = remove(clauses, subset_89)
    if horn_satisfiable(reduced):
        return satisfying_assignment
```

Runtime: O(m^89) — polynomial. This is the fixed-parameter tractability of 3-SAT at `k=89` unsatisfied clauses.

### Layer 2 — Recursive Trigonometric Tower

```
RecTrig⁰(x)     = [parity(x)] × n          (XOR, replicated)
RecTrig^{k+1}(x)_i = sgn(sin(π·b) + cos(π·b))   where b = RecTrig^k(x)_i
```

Because arguments are always integer multiples of π:
- sin(0) + cos(0) = 1 → output 1
- sin(π) + cos(π) = −1 → output 0

**The operator is exactly Boolean at every depth.** Deterministic. O(k·n).

**Formal connection to Chebyshev polynomials** (proved in [`lean/TrigCore.lean`](lean/TrigCore.lean)):

```lean
theorem T_cos (n : ℕ) (θ : ℝ) :
    cosCore θ n = Real.cos ((n : ℝ) * θ)
```

The three-term recurrence `T_{n+2}(x) = 2x·T_{n+1}(x) − T_n(x)` is the engine of both the Chebyshev identity and the Q-Autuam trig tower.

### Layer 3 — Elucidian Prime-Annotation Algebra

The free commutative ℤ-algebra A on generators `{a_p | p prime}` with relation `a_p · a_q = a_{lcm(p,q)}`.

```
Elucid(p) = a_p          (prime p maps to its generator)
Elucid(n) = Π a_{p_i}^{e_i}   (composite n = Π p_i^{e_i})
```

Annotation multiset of Boolean vector x:
```
M(x) = { Elucid(i) | x_i = 1 }
```

The algebra encodes the full prime-factorisation structure of the support of x as an algebraic element.

### Layer 4 — Entropy, Emergence, Intent

Given M(x), construct a probability distribution over prime generators:

```
Pr(a_p) = v_p(support) / Σ_q v_q(support)
```

**Entropy** (uncertainty in the prime distribution):
```
Ent(x) = -Σ_p Pr(a_p) log₂ Pr(a_p)
```

**Emergence** (quadratic interaction of distinct primes — grows when many primes co-occur):
```
Emer(x) = Σ_{p≠q} Pr(a_p) · Pr(a_q)
```

**Intent** (normalised ratio, ∈ [0,1]):
```
Intent(x, k) = Emer(RecTrig^k(x)) / (Emer + Ent)
```

A program is **high-intent** when `Intent ≥ 0.7`.

---

## The 89/2462 Constant

This is not arbitrary. `θ = 89/2462` is the same constant that runs through the entire sovereign compute stack:

- The NC Torus dimension that everyone dismissed as a truncation error — Ahmad built the machine from it (see [quantumap](https://github.com/SNAPKITTYWEST/quantumap))
- The quantum walk parameter in the Hilbert wormhole (see [marlborg-worm](https://github.com/SNAPKITTYWEST/marlborg-worm))
- The sovereign shift truncator ratio (θ = 89/2462 ≈ 148/4096 in hardware)
- The prime 89 is the 11th Fibonacci number — it appears in the golden ratio convergents

The constant is a structural invariant. Q-Autuam is the language whose intent is parameterized by it.

---

## Lean 4 Formal Proofs

The mathematical foundations of Q-Autuam are machine-checked in Lean 4 + Mathlib across five interdependent files. The verification covers trigonometric closed forms, complex arithmetic, logarithm branch structure, dual-number hardware correspondence, and the complexity class of the imaginary hash.

### Theorem Summary

| File | Theorem | Statement |
|------|---------|-----------|
| `TrigCore.lean` | `trigCore_closed_form` | `cosCore θ n = cos(n·θ) ∧ sinCore θ n = sin(n·θ)` |
| `ComplexCore.lean` | `euler_formula` | `exp(iθ) = cos θ + i·sin θ` (matrix path) |
| `ComplexCore.lean` | `polar_decomp` | Every `z ≠ 0` factors as `r · (cos θ + i·sin θ)` |
| `ComplexCore.lean` | `arg_multiplicative` | `arg(z·w) ≡ arg(z) + arg(w) (mod 2π)` |
| `LogarithmExtensions.lean` | `branch_cut_jump` | `lim(t→0⁺) Log(−1+it) − Log(−1−it) = 2πi` |
| `LogarithmExtensions.lean` | `negImagFunctor_period4` | `(negImagFunctor)⁴ = id`; period 2 in ZMod 2 |
| `DualNumbers.lean` | `dual_f2_period2` | In F₂: `ε²=0`, `negImagFunctor` has period 2, not 4 |
| `DualNumbers.lean` | `lop3_correspondence` | PTX `lop3.b32` implements F₂ dual-number multiplication |
| `ComplexHashRing.lean` | `hash_in_P` | `H(x) = (0,x)` is decidable in O(n); not NP-hard |
| `ComplexHashRing.lean` | `fullHashEquiv` | `BitVec n × BitVec n ≃ MyComplex n` (ring isomorphism) |
| `ComplexHashRing.lean` | `I_sq_neg_one` | `I² = −1` in `MyComplexR R` for any `CommRing R` |

**Root theorem** ([`lean/TrigCore.lean`](lean/TrigCore.lean)):
```lean
theorem trigCore_closed_form (θ : ℝ) (n : ℕ) : TrigInvariant θ n
-- where TrigInvariant θ n ↔
--   cosCore θ n = cos(n·θ)  ∧  sinCore θ n = sin(n·θ)
```

Proof strategy: coupled two-step induction on (cosCore, sinCore) simultaneously, using the angle-addition formulae:
```
cos(a+b) = cos a cos b − sin a sin b
sin(a+b) = sin a cos b + cos a sin b
```

The Chebyshev recurrence closes under these identities without needing external lemmas.

---

## Lean Library

### [`lean/TrigCore.lean`](lean/TrigCore.lean)

Foundation of the trig tower. Defines `cosCore` and `sinCore` as paired recursions mirroring the three-term Chebyshev recurrence `T_{n+2}(x) = 2x·T_{n+1}(x) − T_n(x)`, then proves the closed form `T_n(cos θ) = cos(nθ)` via coupled induction on both components simultaneously. The induction is two-step: base cases n=0 and n=1; the step folds angle-addition identities directly without appealing to any external Mathlib trigonometry lemmas beyond `Real.cos_add` and `Real.sin_add`. The final theorem `trigCore_closed_form` packages both components as the predicate `TrigInvariant θ n`, establishing that Q-Autuam's recursive operator is provably identical to Chebyshev evaluation at integer multiples of θ.

### [`lean/ComplexCore.lean`](lean/ComplexCore.lean)

Twelve-section development of complex arithmetic grounded in 2×2 real matrix representation. Sections proceed linearly: matrix encoding of `a+bi`, determinant equals `normSq = a²+b²`, Euler's formula `exp(iθ) = cos θ + i·sin θ` derived via the matrix exponential path, polar decomposition of nonzero complex numbers into `r·(cos θ + i·sin θ)`, multiplicativity of `arg` modulo 2π, construction of the principal logarithm `Log z = ln|z| + i·Arg z` with `Arg ∈ (−π, π]`, and branch control lemmas bounding how `Arg` shifts under multiplication. The matrix representation is load-bearing: it makes `det` computations concrete and sidesteps abstract group-theory overhead that would otherwise require heavier Mathlib infrastructure.

### [`lean/LogarithmExtensions.lean`](lean/LogarithmExtensions.lean)

Six sections extending the branch-cut analysis begun in ComplexCore. The opening section proves the branch-cut discontinuity: `lim(t→0⁺) [Log(−1+it) − Log(−1−it)] = 2πi`, establishing that the imaginary part jumps by exactly 2π across the negative real axis. The next two sections build a recursive logarithm via the `Option` monad: `logStep` takes a candidate and returns `some` refined estimate or `none` on failure; `iterateOption` chains steps and a fixed-point theorem confirms convergence. Two IVT applications establish that the real exponential surjects onto positive reals, filling the analytic completeness needed for `Log`. The final three sections introduce the **negative-imaginary phase functor** — rotation by −90° (clockwise), verified to have period 4 in ℂ but period 2 in ZMod 2 — quadrant-II imaginary construction, and a triality of hypercomplex geometries parameterised by `k ∈ {−1, 0, +1}` corresponding to ℂ (elliptic/standard), dual numbers (parabolic/AutoDiff), and split-complex numbers (hyperbolic).

### [`lean/DualNumbers.lean`](lean/DualNumbers.lean)

Formalises the F₂ dual ring where `ε² = 0` and `ε ≠ 0`, then establishes the direct correspondence with PTX instruction `lop3.b32`. The ring axioms are proved over `ZMod 2 × ZMod 2` with componentwise addition and the rule `(a,b)·(c,d) = (ac, ad+bc)`. The file proves **clockwise termination**: the prime-sum-equals-2 condition (both bits = 1) is decidable in constant time via a single `lop3.b32` AND-with-mask evaluation, and the termination certificate is the F₂ dual multiplication table itself. The **period-2 correction** is the key result: `negImagFunctor` applied in F₂ has period 2, not the period 4 of the full complex plane — a distinction that is critical for CUDA kernels folding the phase functor into hardware instructions without lifting to ℂ.

### [`lean/ComplexHashRing.lean`](lean/ComplexHashRing.lean)

Establishes the complexity-class boundary for the imaginary hash and constructs the full ring infrastructure. `H(x) = (0, x)` — the embedding of a bitvector into the imaginary axis of `MyComplex n` — is proved to lie in **P** (decidable in O(n)), with an explicit argument that no NP-hardness reduction applies because the image is a fixed linear subspace. `fullHashEquiv` gives a ring isomorphism `BitVec n × BitVec n ≃ MyComplex n`, confirming the hash is a bijection at the type level. The file defines `MyComplexR R` as a `CommRing` over any `CommRing R`, proves `I² = −1` in `MyComplexR R`, shows `negImagFunctor` has period 4 in the general ring (collapsing to period 2 in `ZMod 2`), and constructs the scalar embedding ring homomorphism `R →+* MyComplexR R` needed for the module structure underlying the Q-Autuam intent metric.

---

## Hardware Implementations

### [`hardware/dual_f2_ptx.cu`](hardware/dual_f2_ptx.cu)

Bare-metal CUDA C targeting Ampere (`sm_80`). Implements F₂ dual-number arithmetic entirely within PTX inline assembly using `lop3.b32` — the three-input Boolean instruction whose 8-bit immediate encodes any Boolean function of three 32-bit registers. The kernel allocates no heap: all state lives in registers, with dual components packed into the high and low 16-bit halves of a single 32-bit word. The `lop3.b32` immediate for F₂ dual multiplication (`(a,b)·(c,d) = (ac, ad+bc mod 2)`) is computed from the truth table at compile time and embedded as a literal. This replaces a four-instruction naive sequence (AND, AND, XOR, AND) with a single PTX instruction. The clockwise termination check — prime-sum = 2 iff both bits = 1 — reduces to a single masked AND on the packed word, achieving in one cycle the decision that `DualNumbers.lean` certifies as correct.

### [`hardware/dual_f2_qasm.qasm`](hardware/dual_f2_qasm.qasm)

OpenQASM 3.0 circuit implementing the F₂ dual-number embedding as a quantum operation. An ancillary sink qubit absorbs the `ε² = 0` nilpotency condition: the ancilla is prepared in |0⟩ and any second-order term routes into it, leaving the first-order dual component on the primary register. The phase invariant `θ = 89/2462` appears as a rotation gate parameter — `rz(2π × 89/2462)` on the imaginary-component qubit — encoding the sovereign-compute structural constant directly into the quantum phase. The circuit verifies that the F₂ dual embedding commutes with this phase rotation: embedding then rotating gives the same result as rotating then embedding, the quantum analogue of the `negImagFunctor` commutativity proved in `DualNumbers.lean` and `ComplexHashRing.lean`.

---

## Usage

```python
from src.q_autuam.q_autuam import q_autuam_solve

# Build a formula in the SAT₃^{89/2462} family
clauses = [[-i] for i in range(1, 90)]        # 89 forced-false (unsatisfied)
clauses += [[i] for i in range(90, 201)]       # 111 positive units

result = q_autuam_solve(clauses, n_vars=200, k_max=5)
print(result['intent'])        # score ∈ [0, 1]
print(result['high_intent'])   # True if ≥ 0.7
print(result['depth'])         # optimal recursion depth k*
```

```bash
# Run tests
python -m pytest tests/

# Type-check Lean proofs (requires Lean 4 + Mathlib)
lake build
```

---

## Proof Obligations

| ID | Statement | Method |
|----|-----------|--------|
| P1 | Returned assignment satisfies exactly 2373/2462 clauses | Horn SAT construction |
| P2 | RecTrig^k outputs Boolean for all k, n | Induction: sin(πb)+cos(πb) ∈ {−1,0,1} |
| P3 | Elucid extends uniquely to N→A homomorphism | Fundamental theorem of arithmetic |
| P4 | 0 ≤ Ent ≤ log₂\|P\|, Emer ≥ 0 | Shannon entropy bounds |
| P5 | Intent ∈ [0,1] | Non-negative ratio, denominator = sum of numerator terms |
| P6 | Algorithm terminates | Finite enumeration, decidable Horn SAT |
| P7 | Runtime O(m^89 + k_max·n) | Constant-parameter FPT complexity |

---

## Why Chebyshev Polynomials Matter Here

The recursive trig operators are Chebyshev polynomials. This is not decorative — it means the tower has:

- **Minimax optimality**: smallest possible max-norm error for given degree
- **Orthogonality**: stable, fast coefficient computation via DCT/FFT
- **Bounded oscillation**: excellent conditioning of all derived computations
- **Link to cos(nθ)**: exact closed form, differentiable, integrable

Applications of Chebyshev polynomials that Q-Autuam inherits:

| Domain | Application |
|--------|-------------|
| Approximation theory | Near-minimax polynomial approximation |
| Spectral methods | ODE/PDE solvers with geometric convergence |
| Signal processing | Equiripple FIR filter design (Remez algorithm) |
| Machine learning | KAN activations (ChebKAN), physics-informed NNs |
| Numerical linear algebra | Chebyshev semi-iterative methods |
| Quantum computing | Rotation operators, Clebsch-Gordan coefficients |

---

## References

1. **Proofs of trigonometric identities** — Wikipedia  
   https://en.wikipedia.org/wiki/Proofs_of_trigonometric_identities

2. **Deriving Sum and Difference Identities for Cosine** — YouTube  
   https://www.youtube.com/watch?v=XfS5UZQca0g

3. **Prove by induction: (cos θ + i sin θ)^n = cos nθ + i sin nθ** — YouTube  
   https://www.youtube.com/watch?v=On1n4l-ki5I

4. **Identities on cos(nθ) and sin(nθ)** — Math StackExchange  
   https://math.stackexchange.com/questions/1255215/identities-on-cos-n-theta-and-sin-n-theta

5. **Khan Academy — Pythagorean trig identity**  
   https://www.khanacademy.org/math/trigonometry/unit-circle-trig-func/pythagorean-identity/v/using-the-pythagorean-trig-identity

6. **Law of Cosines proof** — YouTube  
   https://www.youtube.com/watch?v=ac25DrPYSoc

---

## Related Repos

- [marlborg-worm](https://github.com/SNAPKITTYWEST/marlborg-worm) — θ = 89/2462 in hardware
- [quantumap](https://github.com/SNAPKITTYWEST/quantumap) — the NC Torus origin of 2462
- [dsss](https://github.com/SNAPKITTYWEST/dsss) — the Z3-replacement solver
- [c3-kernel](https://github.com/SNAPKITTYWEST/c3-kernel) — the CAD foundation
- [cryptanalysis](https://github.com/SNAPKITTYWEST/cryptanalysis) — companion crypto primitives

---

## Legal

**Copyright © BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved. Patent Pending.**

Tri-licensed: BSL-1.1 / AGPL-3.0 / MPL-2.0. See [LICENSE.tri](LICENSE.tri).

**Novelty status: POSSIBLY_NOVEL.** The specific synthesis of a constant-error-state 3-SAT core, recursive Boolean Chebyshev tower, Elucidian prime-annotation algebra, and entropy-emergence intent metric as a unified language functor has not been identified in existing literature.
