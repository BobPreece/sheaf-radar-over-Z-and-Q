"""Guardrail C Stateless Original-ID Junker's QuickXplain (l_0 MUS),
Reiter Hitting-Set Minimal Correction Subsets (MCS), and l_2 Hodge Smearing Comparator.

Strictly Python 3 stdlib only.
"""

from collections import deque
from dataclasses import dataclass
import math
import time
from typing import Callable, Dict, FrozenSet, List, Optional, Sequence, Set

from . import float64_baseline as fb
from .cellular_complex import CellularSheaf1Complex, Simplicial2Complex
from .sparse_exact import solve_torsor


@dataclass
class MUSReport:
    mus_ids: List[int]
    total_cells: int
    oracle_calls: int
    cache_hits: int
    theoretical_qx_bound: float
    verified_minimal: bool
    elapsed_ms: float


@dataclass
class MCSReport:
    mcs_list: List[List[int]]
    oracle_calls: int
    verified_all_minimal: bool
    elapsed_ms: float


@dataclass
class SmearingComparison:
    total_edges: int
    true_culprit_size: int
    l2_dirichlet_energy: float
    l2_innocent_energy_pct: float
    l2_innocent_edges_blamed: int
    l2_innocent_edges_blamed_pct: float
    l2_top_k_precision: float
    l2_top_k_recall: float
    l2_edge_blames: List[float]
    l0_mus_ids: List[int]
    l0_precision: float
    l0_recall: float
    l0_false_blame_pct: float
    l0_oracle_calls: int
    l0_verified_minimal: bool
    l0_elapsed_ms: float


def quickxplain_mus(
    cell_ids: Sequence[int],
    is_unsat_fn: Callable[[Sequence[int]], bool],
    background_ids: Sequence[int] = (),
    verify_minimality: bool = True,
) -> MUSReport:
    """Junker's QuickXplain algorithm over ORIGINAL cell IDs (Guardrail C)."""
    t0 = time.perf_counter()
    cache: Dict[FrozenSet[int], bool] = {}
    calls = 0
    hits = 0

    def oracle(subset: Sequence[int]) -> bool:
        nonlocal calls, hits
        key = frozenset(subset)
        cached = cache.get(key)
        if cached is not None:
            hits += 1
            return cached
        calls += 1
        res = is_unsat_fn(sorted(key))
        cache[key] = res
        return res

    bg = list(background_ids)
    cand = list(cell_ids)

    if oracle(bg):
        return MUSReport([], len(cand), calls, hits, 0.0, True, round((time.perf_counter() - t0) * 1000.0, 3))
    if not oracle(bg + cand):
        raise ValueError("QuickXplain precondition failed: full complex is SAT, no MUS exists!")

    def qx(B: List[int], D: List[int], C: List[int]) -> List[int]:
        if D and oracle(B):
            return []
        if len(C) == 1:
            return C
        mid = len(C) // 2
        C1, C2 = C[:mid], C[mid:]
        D2 = qx(B + C1, C1, C2)
        D1 = qx(B + D2, D2, C1)
        return D1 + D2

    mus = sorted(qx(bg, [], cand))
    k, m = len(mus), len(cand)
    bound = (2.0 * k * math.log2(m / k) + 2.0 * k) if (k > 0 and m >= k) else 0.0
    elapsed = (time.perf_counter() - t0) * 1000.0

    verified = True
    if verify_minimality:
        if not is_unsat_fn(bg + mus):
            verified = False
        else:
            for e in mus:
                if is_unsat_fn(bg + [x for x in mus if x != e]):
                    verified = False
                    break
        assert verified, f"Guardrail C MUS minimality audit FAILED for {mus}!"

    return MUSReport(
        mus_ids=mus,
        total_cells=m,
        oracle_calls=calls,
        cache_hits=hits,
        theoretical_qx_bound=round(bound, 2),
        verified_minimal=verified,
        elapsed_ms=round(elapsed, 3),
    )


def find_mcs_hitting_set(
    cell_ids: Sequence[int],
    is_unsat_fn: Callable[[Sequence[int]], bool],
    max_mcs: int = 8,
    max_mcs_size: int = 4,
    verify_minimality: bool = True,
) -> MCSReport:
    """Reiter's Hitting-Set BFS tree for exact Minimal Correction Subsets (MCS)."""
    t0 = time.perf_counter()
    all_set = list(cell_ids)
    oracle_calls = 0

    def wrapped_unsat(sub: Sequence[int]) -> bool:
        nonlocal oracle_calls
        oracle_calls += 1
        return is_unsat_fn(sub)

    mcs_found: List[FrozenSet[int]] = []
    seen_nodes: Set[FrozenSet[int]] = {frozenset()}
    queue: deque = deque([frozenset()])

    while queue and len(mcs_found) < max_mcs:
        removed: FrozenSet[int] = queue.popleft()
        if any(m.issubset(removed) for m in mcs_found):
            continue
        remaining = [e for e in all_set if e not in removed]
        if not wrapped_unsat(remaining):
            mcs_found.append(removed)
            continue
        if len(removed) >= max_mcs_size:
            continue
        mus_rep = quickxplain_mus(remaining, wrapped_unsat, verify_minimality=False)
        for e in mus_rep.mus_ids:
            nxt = removed | {e}
            if nxt not in seen_nodes and not any(m.issubset(nxt) for m in mcs_found):
                seen_nodes.add(nxt)
                queue.append(nxt)

    mcs_sorted = [sorted(s) for s in mcs_found]
    verified = True
    if verify_minimality:
        for s in mcs_sorted:
            s_set = set(s)
            rem = [e for e in all_set if e not in s_set]
            if is_unsat_fn(rem):
                verified = False
                break
            for e in s:
                if not is_unsat_fn(rem + [e]):
                    verified = False
                    break
        assert verified, f"MCS minimality verification FAILED for {mcs_sorted}"

    return MCSReport(
        mcs_list=mcs_sorted,
        oracle_calls=oracle_calls,
        verified_all_minimal=verified,
        elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
    )


def localize_1complex_mus(
    sheaf: CellularSheaf1Complex,
    ring: Optional[str] = None,
    include_anchors: bool = True,
    verify_minimality: bool = True,
) -> MUSReport:
    use_ring = ring or sheaf.ring
    all_edge_ids = list(range(len(sheaf.edges)))

    def is_unsat_edges(subset_edge_ids: Sequence[int]) -> bool:
        A_sub, c_sub, _ = sheaf.build_coboundary(
            edge_subset=subset_edge_ids, include_anchors=include_anchors
        )
        res = solve_torsor(A_sub, c_sub, ring=use_ring, want_witness=False)
        return res.status in ("UNSAT_FREE_COHOMOLOGY", "UNSAT_TORSION")

    return quickxplain_mus(all_edge_ids, is_unsat_edges, verify_minimality=verify_minimality)


def localize_2complex_h2_mus(
    complex_2d: Simplicial2Complex,
    ring: str = "Z",
    verify_minimality: bool = True,
) -> MUSReport:
    all_face_ids = list(range(len(complex_2d.faces)))

    def is_unsat_faces(subset_face_ids: Sequence[int]) -> bool:
        D1_sub, d_sub = complex_2d.build_delta1(face_subset=subset_face_ids)
        res = solve_torsor(D1_sub, d_sub, ring=ring, want_witness=False)
        return res.status in ("UNSAT_FREE_COHOMOLOGY", "UNSAT_TORSION")

    return quickxplain_mus(all_face_ids, is_unsat_faces, verify_minimality=verify_minimality)


def evaluate_l2_smearing_vs_quickxplain(
    sheaf: CellularSheaf1Complex,
    true_culprit_edge_ids: Sequence[int],
    blame_rel_threshold: float = 0.01,
) -> SmearingComparison:
    A, c, _ = sheaf.build_coboundary(include_anchors=True)
    m = len(sheaf.edges)
    assert A.nrows == m
    _, _, energy, edge_blames = fb.l2_hodge_harmonic_cg(
        A.nrows, A.ncols, A.rows, [float(v) for v in c], max_iter=4000, tol=1e-13
    )
    culprit_set = set(true_culprit_edge_ids)
    k = len(culprit_set)
    innocent_ids = [e for e in range(m) if e not in culprit_set]
    innocent_energy = sum(edge_blames[e] for e in innocent_ids)
    max_blame = max(edge_blames) if edge_blames else 0.0
    thresh = blame_rel_threshold * max_blame
    innocent_blamed = sum(1 for e in innocent_ids if edge_blames[e] >= thresh)
    innocent_blamed_pct = (100.0 * innocent_blamed / len(innocent_ids)) if innocent_ids else 0.0

    top_k = set(sorted(range(m), key=lambda e: edge_blames[e], reverse=True)[:k])
    tp_l2 = len(top_k & culprit_set)
    l2_prec = tp_l2 / k if k > 0 else 1.0

    mus_rep = localize_1complex_mus(sheaf, ring=sheaf.ring, include_anchors=True, verify_minimality=True)
    mus_set = set(mus_rep.mus_ids)
    tp_l0 = len(mus_set & culprit_set)
    l0_prec = tp_l0 / len(mus_set) if mus_set else 1.0
    l0_rec = tp_l0 / k if k > 0 else 1.0

    return SmearingComparison(
        total_edges=m,
        true_culprit_size=k,
        l2_dirichlet_energy=energy,
        l2_innocent_energy_pct=round(100.0 * innocent_energy, 2),
        l2_innocent_edges_blamed=innocent_blamed,
        l2_innocent_edges_blamed_pct=round(innocent_blamed_pct, 2),
        l2_top_k_precision=round(l2_prec, 4),
        l2_top_k_recall=round(l2_prec, 4),
        l2_edge_blames=edge_blames,
        l0_mus_ids=mus_rep.mus_ids,
        l0_precision=round(l0_prec, 4),
        l0_recall=round(l0_rec, 4),
        l0_false_blame_pct=round(100.0 * (1.0 - l0_prec), 2),
        l0_oracle_calls=mus_rep.oracle_calls,
        l0_verified_minimal=mus_rep.verified_minimal,
        l0_elapsed_ms=mus_rep.elapsed_ms,
    )
