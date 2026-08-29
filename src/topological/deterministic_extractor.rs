// Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.
// Patent Pending.
//
// deterministic_extractor.rs — Deterministic Preimage Extractor (Rust)
// --------------------------------------------------------------------
// Source: Ahmad's ORIGINAL_ALGORITHM_ENGINE personas (2026-08-29).
// Implements the Higher-Order Witness Function proven in Lean
// (TopologicalVerification.lean §11: carry_knot_reversible_of_ne) and
// specified in Agda (agda/TPE1/SHA256/Invariants.agda).
//
// CORRECTED guard: reversible iff b != cin (XOR, off-diagonal).
// The persona claimed b ∨ cin; counterexamples (T,T) with out=false and
// (F,F) with out=true disprove it. Both (F,F) and (T,T) are singular.
// See Lean: carry_knot_singularity, carry_knot_dual_singularity.
//
// Honest scope: this extractor performs O(1) algebraic unrolling *per bit*
// *only outside* the singularity horizon. Finding the horizon still requires
// exponential search (see complexity_budget.rs, TOPOLOGICAL_SAT_SPEC.md).
// It does NOT achieve O(1) SHA-256 preimage or break one-wayness.
// Total classical cost remains Θ(2^n); quantum Θ(2^{n/2}) via Grover.

#[inline]
fn carry_knot(a: bool, b: bool, cin: bool) -> bool {
    (a & b) ^ (cin & (a ^ b))
}

#[inline]
fn is_singularity(b: bool, cin: bool) -> bool {
    b == cin // both (F,F) and (T,T) singular; off-diagonal reversible
}

/// The exact Rust translation of the Lean witness (carry_knot_reversible_of_ne).
/// Returns Some(a) on the reversible locus (b != cin), None at singularities
/// where no a satisfies K(a,b,cin)=out.
/// Mirrors Agda `witness` and Lean `carry_knot_reversible_of_ne`.
#[inline(always)]
pub fn carry_knot_witness(b: bool, cin: bool, out: bool) -> Option<bool> {
    match (b, cin, out) {
        // Reversible locus: b != cin → bijection, witness is `out`
        (true, false, _) => Some(out),
        (false, true, _) => Some(out),
        // Erasure singularity (F,F) → output always 0
        (false, false, false) => Some(false), // any a works; return canonical false
        (false, false, true) => None,        // no witness (carry_knot a F F =0 ∀ a)
        // Saturation singularity (T,T) → output always 1
        (true, true, true) => Some(false), // any a works; return canonical false
        (true, true, false) => None,       // no witness (carry_knot a T T =1 ∀ a)
    }
}

/// Placeholder for the topological intermediate state at the singularity horizon.
/// In the real TPE-1 this holds the 64×32 carry matrix after RTX 3080 collapse.
#[derive(Debug, Clone)]
pub struct TopologicalState {
    /// 64 rounds × 32 bits of (b, cin, out) after forward sieve
    /// None = singular (no recovery possible for that bit without brute force)
    pub carry_matrix: Vec<Vec<(bool, bool, bool)>>,
}

impl TopologicalState {
    pub fn get_b(&self, round: usize, bit: usize) -> bool { self.carry_matrix[round][bit].0 }
    pub fn get_cin(&self, round: usize, bit: usize) -> bool { self.carry_matrix[round][bit].1 }
    pub fn get_out(&self, round: usize, bit: usize) -> bool { self.carry_matrix[round][bit].2 }
    pub fn set_a(&mut self, _round: usize, _bit: usize, _a: bool) { /* store recovered a */ }
}

/// Aligns target hash with collapsed intermediate state (stub).
pub fn align_state_vectors(_target_hash: &[u32; 8], singularity_state: &TopologicalState) -> TopologicalState {
    singularity_state.clone()
}

/// Decodes W[0..15] message schedule into 64 bytes (stub).
pub fn decode_message_schedule(_state: &TopologicalState, out: &mut [u8]) {
    out.fill(0)
}

/// Deterministic extractor: walks backward 63→0, 31→0 using the witness.
/// Caller must have first found a non-singular horizon via the sieve;
/// bits where is_singularity(b,cin) is true are skipped (they contribute
/// 2-way ambiguity, not a unique preimage).
pub struct DeterministicExtractor {
    pub target_hash: [u32; 8],
}

impl DeterministicExtractor {
    pub fn new(target_hash: [u32; 8]) -> Self { Self { target_hash } }

    /// Certified witness — matches Lean/Agda. Returns None if called at singularity
    /// with incompatible out (caller should have filtered via is_singularity).
    #[inline(always)]
    pub fn carry_knot_witness(b: bool, cin: bool, out: bool) -> Option<bool> {
        carry_knot_witness(b, cin, out)
    }

    /// O(64·32) = O(1) per-bit algebraic back-propagation *post-horizon*.
    /// Honest bound: overall preimage search is still exponential; this phase
    /// is linear in block size, not a break.
    pub fn unroll_preimage(&self, singularity_state: TopologicalState) -> Result<Vec<u8>, &'static str> {
        let mut current_state = align_state_vectors(&self.target_hash, &singularity_state);
        let mut recovered = vec![0u8; 64];

        for round in (0..64).rev() {
            for bit_idx in (0..32).rev() {
                if round >= current_state.carry_matrix.len() { continue; }
                if bit_idx >= current_state.carry_matrix[round].len() { continue; }
                let b = current_state.get_b(round, bit_idx);
                let cin = current_state.get_cin(round, bit_idx);
                let out = current_state.get_out(round, bit_idx);

                // Guard: singular horizon → skip or brute-force (2-way)
                if is_singularity(b, cin) {
                    // At (F,F) out must be 0, at (T,T) out must be 1; otherwise
                    // the state is inconsistent (no preimage for this path).
                    let expected = carry_knot(false, b, cin);
                    if out != expected {
                        return Err("singular horizon inconsistency: no preimage for this branch");
                    }
                    current_state.set_a(round, bit_idx, false); // canonical
                    continue;
                }

                let a = Self::carry_knot_witness(b, cin, out)
                    .ok_or("witness failed on reversible locus (bug)")?;
                // Round-trip check (mirrors Circom computed_out === out)
                debug_assert_eq!(carry_knot(a, b, cin), out);
                current_state.set_a(round, bit_idx, a);
            }
        }

        decode_message_schedule(&current_state, &mut recovered);
        Ok(recovered)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_witness_reversible() {
        assert_eq!(carry_knot_witness(true, false, true), Some(true));
        assert_eq!(carry_knot_witness(true, false, false), Some(false));
        assert_eq!(carry_knot_witness(false, true, true), Some(true));
        assert_eq!(carry_knot_witness(false, true, false), Some(false));
        // Round-trip
        for b in [true, false] {
            for cin in [true, false] {
                for out in [true, false] {
                    if let Some(a) = carry_knot_witness(b, cin, out) {
                        assert_eq!(carry_knot(a, b, cin), out);
                    }
                }
            }
        }
    }

    #[test]
    fn test_witness_singularities_none() {
        assert_eq!(carry_knot_witness(false, false, true), None);
        assert_eq!(carry_knot_witness(true, true, false), None);
        assert_eq!(carry_knot_witness(false, false, false), Some(false));
        assert_eq!(carry_knot_witness(true, true, true), Some(false));
    }

    #[test]
    fn test_unroll_no_panic() {
        let state = TopologicalState {
            carry_matrix: vec![vec![(true, false, true); 32]; 64],
        };
        let extractor = DeterministicExtractor::new([0u32; 8]);
        let out = extractor.unroll_preimage(state).unwrap();
        assert_eq!(out.len(), 64);
    }
}
