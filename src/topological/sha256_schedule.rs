// Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.
// Patent Pending.
//
// sha256_schedule.rs — Safe Rust message-schedule expansion (W[t])
// --------------------------------------------------------------------
// Mirrors lean/SHA256Schedule.lean (Array.get with proofs) and
// lean/SHA256CarryMatrix.lean CSA trace for schedule words.
//
// SHA-256 FIPS 180-4 §6.2.2:
//   W[t] = W[t-16] + σ0(W[t-15]) + W[t-7] + σ1(W[t-2])   for 16 ≤ t < 64
//   σ0(x) = ROTR 7(x) ⊕ ROTR 18(x) ⊕ SHR 3(x)
//   σ1(x) = ROTR 17(x) ⊕ ROTR 19(x) ⊕ SHR 10(x)
//
// Safety: mirrors Lean's 16 ≤ w.size guard and Array.get ⟨idx, proof⟩.
// Rust uses Vec<u32> with debug_assert! on indices; the schedule is
// always 16 → 64 via build_schedule_aux(48, initial).

/// SHA-256 word
pub type Word = u32;
pub type Block = [Word; 16];
pub type Schedule = [Word; 64];

#[inline(always)]
pub fn small_sigma0(x: Word) -> Word {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

#[inline(always)]
pub fn small_sigma1(x: Word) -> Word {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

pub fn initial_schedule(block: &Block) -> Vec<Word> {
    block.to_vec() // size 16
}

pub fn extend_schedule(w: &mut Vec<Word>) {
    debug_assert!(w.len() >= 16, "extend_schedule requires w.len >=16, got {}", w.len());
    debug_assert!(w.len() < 64, "extend_schedule would exceed 64");
    let t = w.len();
    // Lean: w.get ⟨t-16,_⟩ etc. — Rust: w[t-16] checked
    let wt = w[t - 16]
        .wrapping_add(small_sigma0(w[t - 15]))
        .wrapping_add(w[t - 7])
        .wrapping_add(small_sigma1(w[t - 2]));
    w.push(wt);
    debug_assert!(w.len() <= 64);
}

pub fn build_schedule_aux(mut w: Vec<Word>, fuel: usize) -> Vec<Word> {
    for _ in 0..fuel {
        extend_schedule(&mut w);
    }
    w
}

pub fn message_schedule_array(block: &Block) -> Vec<Word> {
    let init = initial_schedule(block);
    debug_assert_eq!(init.len(), 16);
    let full = build_schedule_aux(init, 48);
    debug_assert_eq!(full.len(), 64);
    full
}

pub fn schedule_of_array(block: &Block) -> Schedule {
    let v = message_schedule_array(block);
    let mut out = [0u32; 64];
    for (i, &w) in v.iter().enumerate() {
        out[i] = w;
    }
    out
}

pub fn is_message_schedule(block: &Block, w: &Schedule) -> bool {
    for i in 0..16 {
        if w[i] != block[i] { return false; }
    }
    for t in 16..64 {
        let expected = w[t - 16]
            .wrapping_add(small_sigma0(w[t - 15]))
            .wrapping_add(w[t - 7])
            .wrapping_add(small_sigma1(w[t - 2]));
        if w[t] != expected { return false; }
    }
    true
}

// ---------------------------------------------------------------------------
// CSA trace for schedule step (4 addends → 2 layers, as in SHA256Schedule.lean)
// W[t] = CSA(W[t-16], σ0(W[t-15]), W[t-7]) → CSA(sum0, carry0, σ1(W[t-2]))
// ---------------------------------------------------------------------------
// Standalone CSA layer definitions (mirrors sha256_csa.rs + SHA256CarryMatrix.lean)
// For Cargo builds this would be `use crate::sha256_csa::{csa_layer, CsaLayer, verify_csa_layer}`.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CsaColumn { pub x: bool, pub y: bool, pub z: bool, pub sum: bool, pub carry: bool }
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CsaLayer { pub inputs: [u32; 3], pub sum: u32, pub carry_bits: u32, pub carry: u32, pub columns: [CsaColumn; 32] }
const ZERO_COLUMN: CsaColumn = CsaColumn { x: false, y: false, z: false, sum: false, carry: false };
fn csa_layer(x: u32, y: u32, z: u32) -> CsaLayer {
    let mut columns = [ZERO_COLUMN; 32];
    let mut sum = 0_u32; let mut carry_bits = 0_u32;
    for i in 0..32 {
        let xi = ((x >> i) & 1) != 0; let yi = ((y >> i) & 1) != 0; let zi = ((z >> i) & 1) != 0;
        let sum_i = xi ^ yi ^ zi; let carry_i = (xi & yi) | (xi & zi) | (yi & zi);
        columns[i] = CsaColumn { x: xi, y: yi, z: zi, sum: sum_i, carry: carry_i };
        sum |= (sum_i as u32) << i; carry_bits |= (carry_i as u32) << i;
        debug_assert_eq!((xi as u8)+(yi as u8)+(zi as u8), (sum_i as u8)+2*(carry_i as u8));
    }
    CsaLayer { inputs: [x,y,z], sum, carry_bits, carry: carry_bits<<1, columns }
}
fn verify_csa_layer(layer: &CsaLayer) {
    let [x,y,z]=layer.inputs;
    assert_eq!(x as u64+y as u64+z as u64, layer.sum as u64+((layer.carry_bits as u64)<<1));
    assert_eq!(x.wrapping_add(y).wrapping_add(z), layer.sum.wrapping_add(layer.carry));
}

#[derive(Debug, Clone)]
pub struct ScheduleStepTrace {
    pub t: usize,
    pub layer0: CsaLayer, // CSA(W[t-16], σ0, W[t-7])
    pub layer1: CsaLayer, // CSA(sum0, carry0, σ1)
    pub w_t: Word,
}

pub fn schedule_step_trace(schedule: &Schedule, t: usize) -> ScheduleStepTrace {
    assert!(16 <= t && t < 64, "t must be 16..63, got {}", t);
    let w16 = schedule[t - 16];
    let s0 = small_sigma0(schedule[t - 15]);
    let w7 = schedule[t - 7];
    let s1 = small_sigma1(schedule[t - 2]);

    let layer0 = csa_layer(w16, s0, w7);
    verify_csa_layer(&layer0);
    let layer1 = csa_layer(layer0.sum, layer0.carry, s1);
    verify_csa_layer(&layer1);

    let w_t = layer1.sum.wrapping_add(layer1.carry);
    let expected = w16.wrapping_add(s0).wrapping_add(w7).wrapping_add(s1);
    assert_eq!(w_t, expected, "schedule CSA final sum mismatch at t={}", t);
    assert_eq!(w_t, schedule[t], "schedule trace does not match schedule array at t={}", t);

    ScheduleStepTrace { t, layer0, layer1, w_t }
}

pub fn compile_schedule_to_traces(schedule: &Schedule) -> Vec<ScheduleStepTrace> {
    (16..64).map(|t| schedule_step_trace(schedule, t)).collect()
}

// ---------------------------------------------------------------------------
// Lean bridge: compact column trace (x,y,z per bit) for verification
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct LeanScheduleColumn {
    pub bit: u8,
    pub x: bool, pub y: bool, pub z: bool,
}

#[derive(Debug, Clone)]
pub struct LeanScheduleMatrix {
    pub t: usize,
    pub layer0: Vec<LeanScheduleColumn>, // 32 cols for layer0
    pub layer1: Vec<LeanScheduleColumn>, // 32 cols for layer1
}

impl From<&ScheduleStepTrace> for LeanScheduleMatrix {
    fn from(trace: &ScheduleStepTrace) -> Self {
        let layer0 = trace.layer0.columns.iter().enumerate().map(|(i,c)| LeanScheduleColumn { bit: i as u8, x: c.x, y: c.y, z: c.z }).collect();
        let layer1 = trace.layer1.columns.iter().enumerate().map(|(i,c)| LeanScheduleColumn { bit: i as u8, x: c.x, y: c.y, z: c.z }).collect();
        LeanScheduleMatrix { t: trace.t, layer0, layer1 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zero_block() -> Block { [0u32; 16] }
    fn sample_block() -> Block {
        let mut b = [0u32; 16];
        for i in 0..16 { b[i] = (i as u32).wrapping_mul(0x9e3779b9); }
        b
    }

    #[test]
    fn test_initial_schedule_size() {
        let v = initial_schedule(&zero_block());
        assert_eq!(v.len(), 16);
    }

    #[test]
    fn test_message_schedule_size_64() {
        let v = message_schedule_array(&zero_block());
        assert_eq!(v.len(), 64);
    }

    #[test]
    fn test_schedule_of_array_correctness() {
        let block = sample_block();
        let sched = schedule_of_array(&block);
        assert!(is_message_schedule(&block, &sched));
        for i in 0..16 { assert_eq!(sched[i], block[i]); }
        for t in 16..64 {
            let expected = sched[t-16].wrapping_add(small_sigma0(sched[t-15])).wrapping_add(sched[t-7]).wrapping_add(small_sigma1(sched[t-2]));
            assert_eq!(sched[t], expected, "mismatch at t={}", t);
        }
    }

    #[test]
    fn test_schedule_step_trace_csa() {
        let block = sample_block();
        let sched = schedule_of_array(&block);
        let trace = schedule_step_trace(&sched, 16);
        assert_eq!(trace.w_t, sched[16]);
        // Verify Lean matrix round-trip
        let lean: LeanScheduleMatrix = (&trace).into();
        assert_eq!(lean.layer0.len(), 32);
        assert_eq!(lean.layer1.len(), 32);
    }

    #[test]
    fn test_compile_schedule_to_traces() {
        let sched = schedule_of_array(&zero_block());
        let traces = compile_schedule_to_traces(&sched);
        assert_eq!(traces.len(), 48);
        for tr in &traces {
            assert_eq!(tr.w_t, sched[tr.t]);
        }
    }

    #[test]
    fn test_fips180_abc_schedule_known() {
        // SHA-256("abc") block (padded, big-endian words): first 3 words are ascii, rest per FIPS
        // We test the schedule invariant, not the exact hash, to avoid full compression.
        let mut block = [0u32; 16];
        block[0] = 0x61626380; // "abc" + 1-bit
        block[15] = 24; // bit-length 24
        let sched = schedule_of_array(&block);
        assert!(is_message_schedule(&block, &sched));
    }
}
