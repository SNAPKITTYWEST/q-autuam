pragma circom 2.1.4;

/*
 * CarryWitnessVerifier.circom — R1CS verifier for the carry-knot witness
 * Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. Patent Pending.
 *
 * Source: Ahmad's persona (DeterministicExtractor → Circom).
 * Corrected to enforce the *corrected* guard b != cin (XOR), not b ∨ cin.
 * The persona's (F,F) and (T,T) singularities are both enforced as
 * forbidden for mismatched out values.
 *
 * Purpose: given private witness a and public b,cin,out, prove that
 *   a = witness(b,cin,out)  AND  carry_knot(a,b,cin) == out
 * over F_p (BN254, via boolean constraints a*(1-a)==0 etc.).
 *
 * Honest scope: proves *forward* correctness of one carry bit.
 * Does NOT prove SHA-256 preimage in O(1). The witness circuit is
 * O(n) constraints (64*32 copies for a full block).
 */

include "circomlib/circuits/gates.circom";
include "circomlib/circuits/comparators.circom";

template CarryWitnessVerifier() {
    signal input b;     // 0/1
    signal input cin;   // 0/1
    signal input out;   // 0/1 (public)
    signal output a;    // 0/1 (private witness)

    // --- Boolean constraints ---
    b * (1 - b) === 0;
    cin * (1 - cin) === 0;
    out * (1 - out) === 0;

    // --- Witness computation: a = witness(b,cin,out) ---
    // Truth table (corrected):
    //   b cin out | a        | notes
    //   1   0   x | x        | reversible
    //   0   1   x | x        | reversible
    //   0   0   0 | 0        | erasure, any a→0, canonical 0
    //   0   0   1 | UNSAT    | no a
    //   1   1   1 | 0        | saturation, any a→1, canonical 0
    //   1   1   0 | UNSAT    | no a
    //
    // Polynomial: a = b*cin*(0) + b*(1-cin)*out + (1-b)*cin*out + (1-b)*(1-cin)*0
    //              with special handling for (T,T)->0 canonical
    // Simplified: a = out * (b ^ cin)   where ^ is XOR = b+cin-2*b*cin
    // But (T,T) with out=1 gives a=0 (since b^cin=0), matches canonical.
    // For UNSAT cases, the round-trip constraint below will fail.

    signal b_xor_cin;
    signal b_and_cin;
    b_and_cin <== b * cin;
    b_xor_cin <== b + cin - 2 * b_and_cin;

    signal out_and_xor;
    out_and_xor <== out * b_xor_cin;

    // For (T,T) we want a=0 even though out_and_xor=0; that's correct.
    // For (F,F) similarly a=0. So a = out AND (b XOR cin)
    a <== out_and_xor;

    a * (1 - a) === 0; // a boolean

    // --- Forbid UNSAT singular cases: if b==cin then out must equal b ---
    // (F,F) → out must be 0, (T,T) → out must be 1
    // Constraint: (1 - b_xor_cin) * (out - b) === 0
    signal one_minus_xor;
    one_minus_xor <== 1 - b_xor_cin;
    signal out_minus_b;
    out_minus_b <== out - b;
    one_minus_xor * out_minus_b === 0;

    // --- Round-trip: carry_knot(a,b,cin) === out ---
    signal a_xor_b;
    signal a_and_b;
    signal cin_and_xor;
    signal out_computed;

    // a XOR b = a + b - 2*a*b
    a_and_b <== a * b;
    a_xor_b <== a + b - 2 * a_and_b;

    // cin AND (a XOR b)
    cin_and_xor <== cin * a_xor_b;

    // carry_knot = (a AND b) XOR (cin AND (a XOR b))
    // XOR = sum -2*prod
    signal prod;
    prod <== a_and_b * cin_and_xor;
    out_computed <== a_and_b + cin_and_xor - 2 * prod;

    out_computed === out;
}

component main {public [out]} = CarryWitnessVerifier();
