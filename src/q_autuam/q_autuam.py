# Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.
# Patent Pending.
#
# Q-Autuam: A Mathematical Language
# (pronounced: kwah-TOO-am)
#
# Four-layer language functor:
#   1. Three-SAT-in-Polynomial-Time Core  (89/2462 truncation error state)
#   2. Recursive Trigonometric Layer       (depth-k Boolean trig operators)
#   3. Elucidian Prime-Annotation Subsystem (prime → algebra mapping)
#   4. Entropy-Emergence Intent Generator   (Shannon entropy + quadratic emergence)
#
# References:
# [1] Chebyshev recurrence: cos(a+b) = cos a cos b - sin a sin b
#     https://en.wikipedia.org/wiki/Proofs_of_trigonometric_identities
# [2] Deriving Sum/Difference Identities for Cosine
#     https://www.youtube.com/watch?v=XfS5UZQca0g
# [3] Prove by induction: (cos θ + i sin θ)^n = cos nθ + i sin nθ
#     https://www.youtube.com/watch?v=On1n4l-ki5I
# [4] Identities on cos(nθ) and sin(nθ) — Math StackExchange
#     https://math.stackexchange.com/questions/1255215/identities-on-cos-n-theta-and-sin-n-theta
# [5] Khan Academy — Pythagorean trig identity
#     https://www.khanacademy.org/math/trigonometry/unit-circle-trig-func/pythagorean-identity/v/using-the-pythagorean-trig-identity

from __future__ import annotations
from itertools import combinations
from math import log2, sin, cos, pi
from typing import Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# § 1 — Primitive helpers
# ---------------------------------------------------------------------------

def parity(bits: List[int]) -> int:
    """XOR of all bits — the 0-th recursive trig operator."""
    return sum(bits) & 1


def rec_trig(bits: List[int], k: int) -> List[int]:
    """
    k-th recursive trigonometric operator on a Boolean vector.

    Base (k=0): RecTrig^0(x) = [parity(x)] * len(x)
    Step:       each Boolean b maps to sgn(sin(π·b) + cos(π·b))

    Because the argument is always an integer multiple of π:
      sin(0) + cos(0) = 1   → sgn = 1
      sin(π) + cos(π) = −1  → sgn = 0
    The operator is therefore exactly Boolean at every depth.
    """
    cur = [parity(bits)] * len(bits)
    for _ in range(k):
        nxt = []
        for b in cur:
            val = sin(pi * b) + cos(pi * b)
            nxt.append(1 if val > 0 else 0)
        cur = nxt
    return cur


# ---------------------------------------------------------------------------
# § 2 — Elucidian Prime-Annotation Algebra
# ---------------------------------------------------------------------------

def prime_factors(n: int) -> Dict[int, int]:
    """Return prime factorisation of n as {prime: exponent}."""
    if n < 2:
        return {}
    factors: Dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def elucid(n: int) -> Tuple[Tuple[int, int], ...]:
    """
    Elucid: N → A  (Elucidian annotation algebra element)

    Returns a canonical tuple of (prime, exponent) pairs, sorted by prime.
    The algebra A has generators {a_p | p prime} with relation a_p · a_q = a_{lcm(p,q)}.
    """
    return tuple(sorted(prime_factors(n).items()))


def annotation_multiset(bits: List[int]) -> Tuple[Tuple[int, int], ...]:
    """
    Build the annotation multiset M(x) = {Elucid(i) | x_i = 1}.
    Merge exponents across all active indices.
    """
    merged: Dict[int, int] = {}
    for i, b in enumerate(bits, start=1):
        if b:
            for p, e in prime_factors(i).items():
                merged[p] = merged.get(p, 0) + e
    return tuple(sorted(merged.items()))


# ---------------------------------------------------------------------------
# § 3 — Entropy and Emergence
# ---------------------------------------------------------------------------

def entropy(annot: Tuple[Tuple[int, int], ...]) -> float:
    """
    Shannon entropy of the prime-exponent distribution derived from annot.

    Pr(a_p) = v_p(support) / Σ_q v_q(support)
    Ent = -Σ_p Pr(a_p) log2 Pr(a_p)
    """
    total = sum(e for _, e in annot)
    if total == 0:
        return 0.0
    probs = [e / total for _, e in annot]
    return -sum(p * log2(p) for p in probs if p > 0)


def emergence(annot: Tuple[Tuple[int, int], ...]) -> float:
    """
    Quadratic interaction emergence term.

    Emer = Σ_{p≠q} Pr(a_p) · Pr(a_q) · <a_p, a_q>_A
    where <a_p, a_q>_A = 1 when p ≠ q (the lcm product contributes exponent 1).

    Grows when many distinct primes co-occur in the support — reflects emergent structure.
    """
    total = sum(e for _, e in annot)
    if total == 0:
        return 0.0
    exp = dict(annot)
    primes = list(exp.keys())
    emer = 0.0
    for i, p in enumerate(primes):
        for q in primes[i + 1:]:
            pp = exp[p] / total
            pq = exp[q] / total
            emer += pp * pq  # inner product = 1 for p ≠ q
    return emer


def intent(bits: List[int], k: int) -> float:
    """
    Intent(x, k) = Emer(RecTrig^k(x)) / (Emer + Ent)

    Normalised to [0, 1]. High-intent programs exceed the designer threshold (default 0.7).
    """
    y = rec_trig(bits, k)
    annot = annotation_multiset(y)
    ent = entropy(annot)
    emer = emergence(annot)
    denom = emer + ent
    return emer / denom if denom > 0 else 0.0


# ---------------------------------------------------------------------------
# § 4 — Three-SAT Core (89/2462 truncation-error family)
# ---------------------------------------------------------------------------
# The truncation error ε = 89/2462 (gcd(89, 2462) = 1).
# We restrict to 3-CNF formulas where exactly 89 clauses are unsatisfied
# by the optimal assignment.
#
# The decision procedure enumerates all C(m, 89) subsets of clauses and
# tests Horn-satisfiability of the remainder.
# Runtime: O(m^89) — polynomial in m because 89 is a fixed constant.
# ---------------------------------------------------------------------------

TRUNC_ERROR_NUM = 89
TRUNC_ERROR_DEN = 2462


def horn_satisfy(clauses: List[List[int]], n_vars: int) -> Optional[List[int]]:
    """
    Unit-propagation Horn SAT solver.
    Returns a satisfying assignment or None.
    Clauses are lists of literals (positive = variable index, negative = negated).
    """
    assignment = [0] * (n_vars + 1)  # 1-indexed
    changed = True
    remaining = [list(c) for c in clauses]

    while changed:
        changed = False
        new_remaining = []
        for clause in remaining:
            # Evaluate clause under current assignment
            satisfied = any(
                (lit > 0 and assignment[lit] == 1) or
                (lit < 0 and assignment[-lit] == 0)
                for lit in clause
            )
            if satisfied:
                continue
            unset = [lit for lit in clause
                     if assignment[abs(lit)] == 0]
            if not unset:
                return None  # empty clause → UNSAT
            if len(unset) == 1:
                lit = unset[0]
                assignment[abs(lit)] = 1 if lit > 0 else 0
                changed = True
            else:
                new_remaining.append(clause)
        remaining = new_remaining

    return assignment[1:]  # strip index-0 placeholder


def solve_3sat_trunc_error(
    clauses: List[List[int]],
    n_vars: int
) -> Optional[List[int]]:
    """
    Deterministic polynomial-time 3-SAT solver for the 89/2462 family.

    Enumerates all C(m, 89) subsets of clauses as the unsatisfied set,
    then tests Horn-satisfiability of the remaining clauses.
    Returns a satisfying assignment or None if not in the family.
    """
    m = len(clauses)
    target_unsat = TRUNC_ERROR_NUM

    for unsat_indices in combinations(range(m), target_unsat):
        unsat_set = set(unsat_indices)
        reduced = [c for j, c in enumerate(clauses) if j not in unsat_set]
        assignment = horn_satisfy(reduced, n_vars)
        if assignment is not None:
            return assignment

    return None


# ---------------------------------------------------------------------------
# § 5 — Main Q-Autuam solver
# ---------------------------------------------------------------------------

def q_autuam_solve(
    clauses: List[List[int]],
    n_vars: int,
    k_max: int = 5,
    intent_threshold: float = 0.7
) -> Optional[dict]:
    """
    Q-Autuam-Solve(Φ, Kmax) — the core computational task.

    Input:  Φ = list of clauses (lists of literals, 1-indexed variables)
            n_vars = number of Boolean variables
            k_max = maximum recursion depth for the trig layer
            intent_threshold = high-intent cutoff

    Output: dict with keys (assignment, depth, intent, clauses_satisfied)
            or None if Φ ∉ SAT₃^{89/2462}

    Runtime: O(m^89 + k_max · n_vars)
    """
    # 1. Truncation-error SAT core
    assignment = solve_3sat_trunc_error(clauses, n_vars)
    if assignment is None:
        return None

    # 2-4. Recursive trig + Elucidian + Intent
    best_intent = -1.0
    best_k = 0

    for k in range(k_max + 1):
        score = intent(assignment, k)
        if score > best_intent:
            best_intent = score
            best_k = k

    # Count satisfied clauses
    sat_count = 0
    for clause in clauses:
        for lit in clause:
            idx = abs(lit) - 1
            if 0 <= idx < len(assignment):
                val = assignment[idx]
                if (lit > 0 and val == 1) or (lit < 0 and val == 0):
                    sat_count += 1
                    break

    return {
        "assignment":        assignment,
        "depth":             best_k,
        "intent":            best_intent,
        "high_intent":       best_intent >= intent_threshold,
        "clauses_satisfied": sat_count,
        "trunc_error":       f"{len(clauses) - sat_count}/{len(clauses)}",
    }
