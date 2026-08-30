# Q-Autuam

[![License: BSL-1.1](https://img.shields.io/badge/license-BSL--1.1-orange?style=flat-square)](LICENSE.tri)
[![License: AGPL-3.0](https://img.shields.io/badge/license-AGPL--3.0-blue?style=flat-square)](LICENSE.tri)
[![License: MPL-2.0](https://img.shields.io/badge/license-MPL--2.0-green?style=flat-square)](LICENSE.tri)
[![Patent Pending](https://img.shields.io/badge/patent-pending-red?style=flat-square)]()
[![theta 89/2462](https://img.shields.io/badge/theta-89%2F2462-gold?style=flat-square)]()
[![Lean 4](https://img.shields.io/badge/Lean-4-Mathlib-5e5086?style=flat-square)](lean/TrigCore.lean)
[![Python 3.11+](https://img.shields.io/badge/Python-3.11%2B-blue?style=flat-square&logo=python)](src/q_autuam/)
[![Rust](https://img.shields.io/badge/Rust-2021-orange?style=flat-square&logo=rust)](src/topological/sha256_csa.rs)

**Pronounced:** *kwah-TOO-am* — **Author:** Ahmad Ali Parr — **Trust:** Bel Esprit D'Accord Irrevocable Trust

> *A program's intent is not what it says it does. It is the ratio of emergence to entropy in its prime-annotated Boolean support, evaluated at the optimal recursive trigonometric depth.*

## What Q-Autuam Is

```
Q : (SAT_3^{89/2462}, RecTrig^(.), Elucid, Ent, Emer) -> (program, Intent)
```

* **SAT_3^{89/2462}** — 3-SAT formulas where optimal assignment leaves exactly 89 clauses unsatisfied (theta=89/2462, p=89 prime, 11th Fibonacci). Solver enumerates C(m,89) subsets and horn_satisfiable remainder.
* **RecTrig** — RecTrig^0=[parity]*n, RecTrig^{k+1}_i = sgn(sin(pi*b)+cos(pi*b)) -> Boolean 0/1 (b in Z).
* **Elucidian** — free comm Z-algebra A={a_p}, M(x)={Elucid(i)|x_i=1} encoding prime support.
* **Ent/Emer/Intent** — Ent=-sum p log2 p, Emer=sum_{p!=q} Pr_p Pr_q, Intent=Emer/(Emer+Ent) in [0,1], high_intent >=0.7.

theta=89/2462 also appears as NC torus dimension, Hilbert wormhole walk parameter, and hardware truncator ratio.

## Directory Layout

```
lean/            — Lean 4 formalizations
src/q_autuam/    — Python language functor
src/topological/ — Rust CSA / schedule / bridge / extractor
hardware/        — PTX / QASM kernels
circuits/        — Circom Groth16 templates
qsharp/          — Q# topological / holographic
spec/            — LANGUAGE_SPEC + topological specs
agda/            — Agda invariants (TPE1)
tests/           — Python tests
```

## Lean

| File | Contains |
|---|---|
| `TrigCore.lean` | cosCore/sinCore via T_{n+2}=2xT_{n+1}-T_n, trigCore_closed_form : cosCore theta n = cos(n*theta) |
| `ComplexCore.lean` | complexToMat, det=normSq, phase theta, exp_I_mul, polar_decomposition, arg_mul, principalLog |
| `LogarithmExtensions.lean` | Branch-cut limits, recursiveLog Option monad, negImagFunctor (-I)*z period 4 / 2 in F2 |
| `DualNumbers.lean` | F2=ZMod 2, DualF2 (primal,tangent) eps^2=0, F_dual swap, lop3.b32 BVDualMul |
| `ComplexHashRing.lean` | MyComplex n (re,im), hash x=(0,x), fullHashEquiv, MyComplexR R CommRing with I^2=-1 |
| `RationalDynamics.lean` | T(z)=2z/(1-z^2) (tan 2theta), T(I)=I, T'(I)=0 |
| `TopologicalVerification.lean` | F2, BraidGen/BraidWord, carry_knot, r1cs_and/xor, dmz_f2_trace (external), SHA256CarryKnot (top_carry_knot, classical_maj, carry_untie_point, avalanche_flatline, carry_knot_singularity/dual_singularity, carry_knot_reversible_of_ne b!=cin, witness) |
| `SHA256CarryMatrix.lean` | Word=BitVec 32, ch/chFast/maj, bitVal/faSum/faCarry, CSAColumn/CarryMatrix=Fin 32->CSAColumn, weighted_fullAdder_correct, weighted_rows_sum/_mod, bigSigma0/1, State, t1/t2/round, csa1/2/3/t1ViaCSA, CarryLayer/CarryTrace, sha256_carry_matrix/t1/t2 |
| `SHA256Schedule.lean` | smallSigma0/1, initialSchedule/extendSchedule/buildScheduleAux/messageScheduleArray (Array Word 16->64), ScheduleInvariant, scheduleOfArray: Fin 64->Word, IsMessageSchedule, ScheduleStepTrace |

## Rust — Topological

| File | Contains |
|---|---|
| `sha256_csa.rs` | CsaColumn/CsaLayer, csa_layer(x,y,z) per-bit Maj, verify_csa_layer, ch/maj/big_sigma0/1, T1Trace (3 CSA + CPA), t1_via_csa/t2_via_csa, Sha256RoundMatrix, LeanCsaMatrix bridge |
| `sha256_schedule.rs` | initial_schedule/extend_schedule/build_schedule_aux/message_schedule_array/schedule_of_array, ScheduleStepTrace (2 CSA per W[t]), LeanScheduleMatrix |
| `aegis_bridge.rs` | BraidWord=Vec<i32>, StabilityAnalysis, SymbolicBraidEngine::free_reduce/mirror_projection, ScalingBenchmark, carry_knot/is_singularity(=b==cin), TopologicalPipeline::generate_singularity_seeds/execute_singularity_sieve |
| `deterministic_extractor.rs` | carry_knot_witness->Option<bool>, TopologicalState, DeterministicExtractor::unroll_preimage 63..0 |
| `complexity_budget.rs` | ComplexityBudget k=(pi/4)sqrt(2^n/S), C_total=k*(Omega+d^2), DecoherenceAnalysis |

## Hardware / Circuits / Q#

* `hardware/dual_f2_ptx.cu` — DualF2 lop3.b32 Ampere sm_80
* `hardware/dual_f2_qasm.qasm` — dual_mul_step ccx, cp(89*pi/1231), F_dual swap
* `hardware/tpu_ptx/topological_annihilate.ptx` — shfl.sync add.s32, 8704 cores
* `circuits/BraidAnnihilator.circom` — IsAnnihilated (in1+in2)*out==0, 1M BraidAnnihilator
* `circuits/CarryWitnessVerifier.circom` — a=out*(b xor cin), (1-xor)*(out-b)==0, carry_knot===out
* `qsharp/topological/HolographicKey.qs` — MaxSeparationUT, CreateHolographicKey, RecoverDigitalKey k=floor(pi/4 sqrt(2^{n-t}))
* `qsharp/topological/PrecisionSensing.qs` — PrecisionSensingProbe, DistillSatisfyingAssignments
* `agda/TPE1/SHA256/Invariants.agda` — carry-knot, witness, IsSingular=b==cin, NotSingular=not(b==cin), invariant-reversibility/unroll

## Specs

* `spec/LANGUAGE_SPEC.md` — language functor Q four layers
* `spec/topological/TOPOLOGICAL_SAT_SPEC.md` — 3-SAT->F->U_T->Q pipeline, C_total
* `spec/topological/HOLOGRAPHIC_KEY_SPEC.md` — U_T, |Psi_Holo>, k iterations
* `spec/topological/HOLOGRAPHIC_WORM_SPEC.md` — H_mu/lambda_L/Sigma_Page/B_multi/Theta_shift mapping

## Usage

```python
from src.q_autuam.q_autuam import q_autuam_solve
clauses = [[-i] for i in range(1,90)] + [[i] for i in range(90,201)]
result = q_autuam_solve(clauses, n_vars=200, k_max=5)
```

```bash
python -m pytest tests/
lean lean/TrigCore.lean  # Lean 4.33.1 + Mathlib (no lakefile in repo)
rustc --edition 2021 --crate-type lib src/topological/sha256_csa.rs -o /tmp/a.rmeta
agda --safe agda/TPE1/SHA256/Invariants.agda
```

## Related

* `cryptanalysis` — circuit functor, truncated hash inverter (QF_BV, H uninterpreted), TruncHashInv.lean, Work G, affine inverter (https://github.com/SNAPKITTYWEST/cryptanalysis)
* `marlborg-worm` / `quantumap` — theta=89/2462 origins
* `dsss` / `c3-kernel` — SMT / CAD

## Legal

Copyright (c) BEL ESPRIT D ACCORD TRUST HOLDINGS INC. Patent Pending. Tri-licensed BSL-1.1 / AGPL-3.0 / MPL-2.0. See LICENSE.tri.
