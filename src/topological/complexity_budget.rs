// Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.
// Patent Pending.
//
// Complexity Budget for Topological Quantum 3-SAT Solver
//
// Architecture: 3-SAT → Complex Manifold F → Unitary U_T → Amplitude Distillation Q
// Protected by: Phase-Biased Surface Code or Topological (Majorana) Protection
//
// Key result: C_total = Θ(2^{n/2} · (m + n + d²))
// Complexity is NOT bypassed — it is reparametrized.

/// Budget parameters for the full topological 3-SAT pipeline.
pub struct ComplexityBudget {
    /// Number of Boolean variables
    pub n_vars: usize,
    /// Number of clauses
    pub m_clauses: usize,
    /// Number of satisfying assignments (1 for hardest case)
    pub num_solutions: usize,
    /// Surface code distance d
    pub code_distance: usize,
}

impl ComplexityBudget {
    /// k ≈ (π/4) · √(2^n / S)  — Grover-style iterations
    pub fn distillation_iterations(&self) -> f64 {
        let two_to_n = (2_f64).powi(self.n_vars as i32);
        (std::f64::consts::PI / 4.0)
            * (two_to_n / self.num_solutions as f64).sqrt()
    }

    /// Ω = O(m + n) — gates per distillation iteration
    pub fn oracle_complexity(&self) -> f64 {
        (self.m_clauses + self.n_vars) as f64
    }

    /// QEC overhead: d² syndrome extractions per iteration (surface code)
    pub fn qec_overhead(&self) -> f64 {
        (self.code_distance * self.code_distance) as f64
    }

    /// C_total = k · (Ω + QEC) = Θ(2^{n/2} · (m + n + d²))
    pub fn total_cycles(&self) -> f64 {
        let k = self.distillation_iterations();
        let omega = self.oracle_complexity();
        let qec = self.qec_overhead();
        k * (omega + qec)
    }

    /// Braid depth for a single clause check:
    ///   D(C_j) = 2d + O(1)
    /// where d = spatial separation of anyons in the lattice.
    /// For m clauses: total braid depth = O(m · d)
    pub fn braid_depth_single_clause(spatial_separation: usize) -> usize {
        2 * spatial_separation + 2 // transport + interaction + restitution
    }

    pub fn total_braid_depth(&self, spatial_separation: usize) -> usize {
        self.m_clauses * Self::braid_depth_single_clause(spatial_separation)
    }
}

/// Decoherence analysis: how many iterations before the system decoheres.
pub struct DecoherenceAnalysis {
    /// Phase-damping rate per iteration
    pub gamma: f64,
    /// sqrt(a) where a = initial probability of satisfying assignment
    pub initial_amp: f64,
    /// Minimum resolvable phase (noise floor)
    pub noise_floor: f64,
}

impl DecoherenceAnalysis {
    /// k_max = ln(1/σ) / γ
    pub fn max_stable_iterations(&self) -> f64 {
        (1.0 / self.noise_floor).ln() / self.gamma
    }

    /// k_opt = π / (4 · sqrt(a))
    pub fn optimal_iterations(&self) -> f64 {
        std::f64::consts::PI / (4.0 * self.initial_amp)
    }

    /// True if the hardware can sustain enough iterations to find the solution.
    pub fn is_inversion_viable(&self) -> bool {
        self.max_stable_iterations() > self.optimal_iterations()
    }

    /// Critical rotation angle θ_crit = π/k
    pub fn critical_theta(k_iterations: usize) -> f64 {
        std::f64::consts::PI / k_iterations as f64
    }

    /// Noise leakage for a near-miss at angular distance α: cos²(α)
    pub fn noise_leakage(alpha: f64) -> f64 {
        alpha.cos().powi(2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_small_instance() {
        let budget = ComplexityBudget {
            n_vars: 20,
            m_clauses: 60,
            num_solutions: 1,
            code_distance: 3,
        };
        let k = budget.distillation_iterations();
        assert!(k > 1000.0 && k < 1200.0, "k ≈ 1100 for n=20");
        let total = budget.total_cycles();
        assert!(total > 8e4 && total < 1.1e5, "C_total ≈ 9.8×10⁴");
    }

    #[test]
    fn test_decoherence_viable() {
        let analysis = DecoherenceAnalysis {
            gamma: 0.0001,   // superconducting qubit
            initial_amp: 0.001,
            noise_floor: 0.01,
        };
        assert!(analysis.is_inversion_viable(), "High-coherence hardware should be viable");
    }

    #[test]
    fn test_decoherence_not_viable() {
        let analysis = DecoherenceAnalysis {
            gamma: 0.1,    // NISQ hardware
            initial_amp: 0.001,
            noise_floor: 0.01,
        };
        assert!(!analysis.is_inversion_viable(), "NISQ hardware should not be viable");
    }

    #[test]
    fn test_braid_depth() {
        let budget = ComplexityBudget {
            n_vars: 10,
            m_clauses: 30,
            num_solutions: 1,
            code_distance: 3,
        };
        // Each clause: 2*5 + 2 = 12 braids (d=5 spatial separation)
        assert_eq!(ComplexityBudget::braid_depth_single_clause(5), 12);
        assert_eq!(budget.total_braid_depth(5), 360);
    }

    #[test]
    fn test_critical_theta() {
        let theta = DecoherenceAnalysis::critical_theta(1000);
        let expected = std::f64::consts::PI / 1000.0;
        assert!((theta - expected).abs() < 1e-12);
    }

    #[test]
    fn test_noise_leakage_perfect_sat() {
        // α = 0 (perfect satisfying assignment): leakage = cos²(0) = 1
        // This means a perfect SAT is indistinguishable before amplification
        assert!((DecoherenceAnalysis::noise_leakage(0.0) - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_noise_leakage_orthogonal() {
        // α = π/2 (orthogonal state): leakage = cos²(π/2) = 0
        let leakage = DecoherenceAnalysis::noise_leakage(std::f64::consts::PI / 2.0);
        assert!(leakage.abs() < 1e-10);
    }
}
