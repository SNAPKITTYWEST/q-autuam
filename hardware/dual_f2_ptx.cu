// Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.
// Patent Pending.
//
// Dual Numbers over F₂ — Bare-Metal PTX Implementation (Ampere SM)
//
// Primal and tangent packed into a single 64-bit register (uint2).
// No heap/stack allocation. Over F₂:
//   addition  = XOR  (^)
//   multiply  = AND  (&)
//   nilpotent ε²=0 + Frobenius 2ab=0 → squaring annihilates tangent
//
// Compiles to PTX lop3.b32 on Ampere (RTX 3080 / RTX 4090 class).

#include <cstdint>

// 64-bit aligned register pair: a + bε  (a=primal, b=tangent)
struct __align__(8) DualF2 {
    uint32_t primal;   // a ∈ {0,1}^32
    uint32_t tangent;  // b ∈ {0,1}^32
};

// ---------------------------------------------------------------------------
// Dual multiplication: (a₁+b₁ε)(a₂+b₂ε) = a₁a₂ + (a₁b₂ ⊕ a₂b₁)ε
// (ε²=0 means the ε² term vanishes)
// Tangent: lop3.b32 with LUT for (x & z) ^ (y & w) on Ampere
// ---------------------------------------------------------------------------
__device__ __forceinline__
DualF2 dual_mul_f2(DualF2 x, DualF2 y) {
    DualF2 z;
    z.primal  = x.primal & y.primal;
    z.tangent = (x.primal & y.tangent) ^ (y.primal & x.tangent);
    return z;
}

// ---------------------------------------------------------------------------
// Dual squaring: (a+bε)² = a² + 2abε = a²
// Over F₂: a²=a (idempotence), 2ab=0 (char 2), ε²=0 (nilpotent)
// Tangent is unconditionally zeroed → maps to a single reset on hardware
// ---------------------------------------------------------------------------
__device__ __forceinline__
DualF2 dual_square_f2(DualF2 x) {
    DualF2 z;
    z.primal  = x.primal;  // a² = a in F₂
    z.tangent = 0;          // 2ab + ε² term → 0
    return z;
}

// ---------------------------------------------------------------------------
// Clockwise quarter-turn functor F(z) = -iz
// Over F₂: -1 = 1, so F(a,b) = (b, a)  [period 2, not 4]
// Note: genuine period-4 requires coefficients where -1 ≠ 1 (e.g. ZMod 5)
// ---------------------------------------------------------------------------
__device__ __forceinline__
DualF2 F_dual(DualF2 x) {
    return {x.tangent, x.primal};
}

// ---------------------------------------------------------------------------
// Period verification (compile-time constant)
//   F_dual(F_dual(x)) = x  (period 2 over F₂)
// ---------------------------------------------------------------------------
__device__ __forceinline__
bool verify_period_two(DualF2 x) {
    DualF2 y = F_dual(F_dual(x));
    return (y.primal == x.primal) && (y.tangent == x.tangent);
}

// ---------------------------------------------------------------------------
// Example kernel: apply dual multiplication across a vector
// ---------------------------------------------------------------------------
__global__
void dual_mul_kernel(
    const DualF2* __restrict__ xs,
    const DualF2* __restrict__ ys,
          DualF2* __restrict__ out,
    int n
) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) out[i] = dual_mul_f2(xs[i], ys[i]);
}
