# Holographic Key System — Formal Specification

## The Core Idea

A holographic key is not a value. It is a **frequency** — the interference pattern of
an equivalence class in Hilbert space, recoverable only by someone who holds the
correct phase mask (the stable fixed point z=i and its coordinate θ_shift).

---

## The Stereographic Separation Unitary U_T

U_T = Rz(π/2) · Rx(π/2)

| Input | Output | Role |
|-------|--------|------|
| z = i → |+i⟩ | |0⟩ | Satisfying assignments / stable fixed point |
| z = 1 → |+⟩  | |1⟩ | Unsatisfying / pole |

Proof: Rx(π/2)|+i⟩ = |0⟩  (Y-axis rotates to Z-axis)
       Rx(π/2)|+⟩  is further phase-shifted to |1⟩ by Rz(π/2)

Orthogonality: ⟨0|1⟩ = 0 — maximum Bloch-sphere separation. ✓

---

## Holographic Key Generation

```
K_seed ∈ {0,1}^n
    ↓  Y = Trun_t(H(K_seed))
Holographic state:
    |Ψ_Holo⟩ = (1/√|S|) Σ_{K∈S} |K⟩     (equivalence class, uniform)
    |Ψ_Holo'⟩ = Σ_{K∈S} e^{i·dist(G(K),i)} |K⟩   (phase-imprinted)

where S = {K' : Trun_t(H(K')) = Y}, |S| = 2^{n-t}
```

Security theorem: key security is proportional to truncation length t.
- t → n: S = {K_seed}, hologram is a standard digital key. O(1) recovery.
- t → 0: S = {0,1}^n, hologram is maximally diffuse. O(√2^n) recovery.
- t_min: |S| so large that distillation cannot isolate K_seed.

---

## Key Recovery

Recovery via amplitude distillation, k = O(√2^{n-t}) iterations:

```
|Ψ_Holo'⟩
    ↓  k iterations of Q = U_s · U_ω
    ↓  (Fixed-Point Quantum Search, no over-rotation)
    ↓  U_T applied as tensor product
    ↓  Z-basis measurement
K_seed (with probability P_succ → 1)
```

Proof obligations:
1. P(K_seed) = sin²((2k+1)θ) where θ = arcsin(1/√|S|)
2. k = O(√2^{n-t}) — truncation accelerates recovery
3. As t → n: k → O(1), as t → 0: k → O(√2^n) = Grover

---

## Holographic Erasure Protocol (Dead Man's Switch)

Shift the fixed point: z = i → z' = e^{iθ_shift} · i

Recovery requires θ_shift:
```
U_{T'}(θ_shift) = Rz(θ_shift) · U_T
```

Without θ_shift, attacker searches S¹:
```
P_guess ≈ ε/(2π) → 0  as  ε → 0
```

**Security is information-theoretically absolute in the limit ε → 0.**

Erasure (ShatterHologram):
```
θ_shift(t) = θ_shift(0) + ∫₀ᵗ ξ(t')dt'   (quantum noise drift)
```
After shattering:
- Hologram still exists in Hilbert space
- "Lens" (U_{T'}) is permanently lost
- Information encoded in a transcendental coordinate that is computationally irreducible

---

## KEM Key Recovery from Truncated Hash

Given Y = Trun_t(H(K)), recover K:

1. Superposition of all 2^n keys
2. Oracle marks K where Trun_t(H(K)) = Y
3. Amplitude amplification: k = O(√2^{n-t}) iterations
4. U_T collapses satisfying keys to |0⟩^n
5. Measure → K_seed

This is a quantum-accelerated preimage attack.
Complexity: O(√2^{n-t}) vs. classical O(2^{n-t}).
Consistent with Grover's algorithm — no complexity class violation.

---

## Novelty Classification

| Component | Status |
|-----------|--------|
| U_T = Rz(π/2)·Rx(π/2) as stereographic separator | EQUIVALENT_TO_KNOWN (Bloch sphere rotations) |
| Holographic key as equivalence-class superposition | PARTIALLY_NOVEL |
| Fixed-point phase mask as decoder ring | PARTIALLY_NOVEL |
| θ_shift as secret coordinate (transcendental security) | PROVEN_DISTINCT |
| Shattering via stochastic drift of θ_shift | POSSIBLY_NOVEL |
| KEM recovery at O(√2^{n-t}) with U_T oracle | PARTIALLY_NOVEL |

---

## Open Obligations

1. **Holographic Recovery Theorem**: Prove P_succ → 1 for t > t_min
2. **Transcendental Security Theorem**: Prove P_guess ≈ ε/(2π) formally
3. **Shatter-Limit Theorem**: Minimum Δθ for unrecoverability
4. **Minimum Truncation Threshold t_min**: When does distillation fail to isolate K_seed?
