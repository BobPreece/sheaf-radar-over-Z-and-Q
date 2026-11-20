"""Cycle 7 — O(1) Fast-Path Incremental Pre-Commit Sheaf Firewall (`IncrementalSheafFirewall`).

Provides transactional streaming agent memory verification with zero floating-point drift:
  - propose_claim(claim) -> FirewallVerdict  (pure read-only pre-commit verification)
  - commit_claim(claim)  -> FirewallVerdict  (commits iff verified consistent; quarantines bad claims!)
  - checkpoint()         -> int
  - rollback(ckpt_id)    -> None

Architecture:
  1. Spanning-Forest Potential Cache (O(1) Fast Path for 1D affine/unit/scale claims over Z/Q):
     - Small-to-large weighted Union-Find caching exact native-int affine potentials
       x_v = (s_num / s_den) * x_root + (b_num / b_den) (ZERO fractions.Fraction!).
     - Tree-edge merge: O(log V) amortized, 0 matrix solves.
     - Commuting corroboration / contradiction: O(1) holonomy check + O(depth) fundamental-cycle MUS!
     - Unit-scale gauge-tightening / Z_m Liar flip: O(1) divisibility & pin check + instant MUS!
     - Non-unit scale / multi-stalk / H^2 2-simplex escalation: localized component exact Z/Q solver.
  2. Multi-Stalk Vector Q-Sheaf Lane (handles non-dyadic Hilbert/Cauchy updates with 0 false rejections).
  3. Simplicial 2-Simplex H^2 Lane (detects triadic & RP^2 torsion traps before commit).
  4. Incremental Tarski Order Lane (dirty-queue BFS interval bound propagation for x_u <= x_v).
  5. Full Clean-Room Batch Audit (`verify_committed_state_from_scratch`) certifying 100% integrity!

Strictly Python 3 stdlib only.
"""

from collections import deque
from dataclasses import dataclass, field
import math
import time
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from .mus_quickxplain import quickxplain_mus
from . import sparse_exact as se

Rat = Tuple[int, int]


def _rn(num: int, den: int) -> Rat:
    if den < 0:
        num, den = -num, -den
    if num == 0:
        return (0, 1)
    g = math.gcd(abs(num), den)
    return (num // g, den // g)


def _radd(a: Rat, b: Rat) -> Rat:
    return _rn(a[0] * b[1] + b[0] * a[1], a[1] * b[1])


def _rsub(a: Rat, b: Rat) -> Rat:
    return _rn(a[0] * b[1] - b[0] * a[1], a[1] * b[1])


def _rmul(a: Rat, b: Rat) -> Rat:
    return _rn(a[0] * b[0], a[1] * b[1])


def _rdiv(a: Rat, b: Rat) -> Rat:
    if b[0] == 0:
        raise ZeroDivisionError("Zero rational division")
    return _rn(a[0] * b[1], a[1] * b[0])


@dataclass
class FirewallClaim:
    """Unified streaming claim envelope for all 4 verification lanes."""

    claim_id: int
    kind: str  # "affine_1d", "anchor_1d", "vector_q", "simplex_h2", "tarski_order", "tarski_bound"
    payload: Dict[str, Any]
    ring: str = "Z"
    label: str = ""


@dataclass
class FirewallVerdict:
    claim_id: int
    accepted: bool
    path_taken: str  # "FAST_TREE_MERGE_O1", "FAST_CORROBORATE_O1", "FAST_GAUGE_PIN_O1",
                     # "FAST_REJECT_FREE_O1", "FAST_REJECT_TORSION_O1",
                     # "ESCALATED_COMPONENT_EXACT", "VECTOR_Q_EXACT", "H2_SIMPLEX_EXACT",
                     # "TARSKI_INCREMENTAL_BFS"
    reason: str
    contradiction_class: Optional[str] = None  # None, "UNSAT_FREE_COHOMOLOGY", "UNSAT_TORSION", "UNSAT_TARSKI_ORDER"
    mus_claim_ids: Optional[List[int]] = None
    torsion_cert: Optional[Tuple[int, int]] = None
    latency_us: float = 0.0


class IncrementalSheafFirewall:
    """Transactional pre-commit exact Z/Q/H^2/Tarski firewall with O(1) spanning-forest cache."""

    def __init__(self, ring: str = "Z") -> None:
        if ring not in ("Z", "Q"):
            raise ValueError(f"ring must be 'Z' or 'Q', got {ring!r}")
        self.ring = ring

        # Committed & quarantined transaction logs
        self.committed_claims: List[FirewallClaim] = []
        self.claim_by_id: Dict[int, FirewallClaim] = {}
        self.quarantine: List[Tuple[FirewallClaim, FirewallVerdict]] = []
        self.checkpoints: Dict[int, int] = {}
        self._next_ckpt_id: int = 1

        # Lane 1: 1D Affine Spanning-Forest Potential Cache (native int rationals!)
        # For each vertex v: x_v = (s_n/s_d) * x_{root} + (b_n/b_d)
        self.comp_root: Dict[int, int] = {}
        self.comp_members: Dict[int, List[int]] = {}
        self.pot_s: Dict[int, Rat] = {}
        self.pot_b: Dict[int, Rat] = {}
        self.tree_adj: Dict[int, List[Tuple[int, int]]] = {}  # v -> [(nbr, claim_id), ...]
        self.comp_pinned: Dict[int, Optional[Rat]] = {}
        self.comp_pin_claim: Dict[int, Optional[int]] = {}
        self.comp_has_nonunit: Dict[int, bool] = {}
        self.comp_claims: Dict[int, List[int]] = {}  # root -> list of committed 1D claim_ids

        # Lane 2: Multi-Stalk Vector Q-Sheaf claims grouped by component key
        self.vec_groups: Dict[str, List[FirewallClaim]] = {}

        # Lane 3: Simplicial 2-Simplex H^2 claims (triadic constraints delta^1 y = d)
        self.h2_claims: List[FirewallClaim] = []

        # Lane 4: Incremental Tarski Order constraints (x_u + offset <= x_v) & integer bounds [lo, hi]
        self.tarski_lo: Dict[int, int] = {}
        self.tarski_hi: Dict[int, int] = {}
        self.tarski_out: Dict[int, List[Tuple[int, int, int]]] = {}  # u -> [(v, offset, claim_id)]
        self.tarski_in: Dict[int, List[Tuple[int, int, int]]] = {}   # v -> [(u, offset, claim_id)]
        self.tarski_claims: List[FirewallClaim] = []

        # Telemetry counters
        self.stats: Dict[str, int] = {
            "total_proposed": 0,
            "total_committed": 0,
            "total_quarantined": 0,
            "fast_o1_hits": 0,
            "escalated_solves": 0,
        }

    def _ensure_vertex_1d(self, v: int) -> None:
        if v not in self.comp_root:
            self.comp_root[v] = v
            self.comp_members[v] = [v]
            self.pot_s[v] = (1, 1)
            self.pot_b[v] = (0, 1)
            self.tree_adj[v] = []
            self.comp_pinned[v] = None
            self.comp_pin_claim[v] = None
            self.comp_has_nonunit[v] = False
            self.comp_claims[v] = []

    def _is_provably_minimal_cycle_mus(
        self, u: int, v: int, closing_claim: FirewallClaim, path_cids: List[int], xr_req: Rat
    ) -> Optional[Tuple[int, int]]:
        """O(L) certificate checking whether the fundamental cycle (path_cids + closing_claim)
        is a provably minimal UNSAT_TORSION MUS:
          1. All edges form a simple cycle v_0 - v_1 - ... - v_L - v_0,
          2. At least one vertex on the cycle has non-integral forced value x_w = s_w * xr_req + b_w,
          3. Either clockwise OR counter-clockwise around the cycle, every directed step (a -> b)
             has |coeff(b)| == 1 (so deleting ANY single edge leaves an open path solvable in Z
             starting at x_start = 0, guaranteeing every proper subset is SAT_INTEGRAL!).
        Returns exact torsion_cert (mod_m, rem_m) if minimal, else None.
        """
        cycle_claims = [self.claim_by_id[cid] for cid in path_cids] + [closing_claim]
        if len(cycle_claims) < 2:
            return None
        # Reconstruct ordered cycle vertices starting from u along path_cids to v, then back to u
        cur = u
        verts_on_cycle: List[int] = [u]
        fwd_ok = True
        rev_ok = True
        for cl in cycle_claims:
            if cl.kind != "affine_1d":
                return None
            eu, ev = int(cl.payload["u"]), int(cl.payload["v"])
            ecu, ecv = abs(int(cl.payload["coeff_u"])), abs(int(cl.payload["coeff_v"]))
            if cur == eu:
                nxt = ev
                c_from, c_to = ecu, ecv
            elif cur == ev:
                nxt = eu
                c_from, c_to = ecv, ecu
            else:
                return None
            if c_to != 1:
                fwd_ok = False
            if c_from != 1:
                rev_ok = False
            cur = nxt
            verts_on_cycle.append(cur)
        if cur != u or (not fwd_ok and not rev_ok):
            return None
        if len(set(verts_on_cycle[:-1])) != len(cycle_claims):
            return None
        for w in verts_on_cycle[:-1]:
            val_w = _radd(_rmul(self.pot_s.get(w, (1, 1)), xr_req), self.pot_b.get(w, (0, 1)))
            if val_w[1] != 1:
                return (val_w[1], val_w[0] % val_w[1])
        return None

    def _tree_path_claims(self, u: int, v: int) -> List[int]:
        """Extract exact spanning-tree path claim IDs between u and v in O(component depth)."""
        if u == v:
            return []
        parent: Dict[int, Tuple[int, int]] = {u: (-1, -1)}
        q = deque([u])
        while q:
            cur = q.popleft()
            if cur == v:
                break
            for nbr, cid in self.tree_adj.get(cur, ()):
                if nbr not in parent:
                    parent[nbr] = (cur, cid)
                    q.append(nbr)
        if v not in parent:
            return []
        path: List[int] = []
        cur = v
        while cur != u:
            prev, cid = parent[cur]
            path.append(cid)
            cur = prev
        path.reverse()
        return path

    def _solve_1d_component_exact(
        self,
        claim_ids: Sequence[int],
        extra_claim: Optional[FirewallClaim] = None,
        want_mus_on_fail: bool = True,
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], Optional[List[int]]]:
        """Localized component compressed-core exact Z/Q verification (escalated lane)."""
        claims = [self.claim_by_id[cid] for cid in claim_ids]
        if extra_claim is not None:
            claims.append(extra_claim)

        def build_and_solve(sub_claims: Sequence[FirewallClaim]) -> se.TorsorResult:
            verts: Dict[int, int] = {}
            for cl in sub_claims:
                if cl.kind == "affine_1d":
                    u, v = cl.payload["u"], cl.payload["v"]
                    if u not in verts:
                        verts[u] = len(verts)
                    if v not in verts:
                        verts[v] = len(verts)
                elif cl.kind == "anchor_1d":
                    v = cl.payload["v"]
                    if v not in verts:
                        verts[v] = len(verts)
            A = se.SparseIntMatrix(len(sub_claims), len(verts))
            c_vec = [0] * len(sub_claims)
            for row_i, cl in enumerate(sub_claims):
                if cl.kind == "affine_1d":
                    iu = verts[cl.payload["u"]]
                    iv = verts[cl.payload["v"]]
                    A.add_entry(row_i, iu, -int(cl.payload["coeff_u"]))
                    A.add_entry(row_i, iv, int(cl.payload["coeff_v"]))
                    c_vec[row_i] = int(cl.payload["rhs"])
                elif cl.kind == "anchor_1d":
                    iv = verts[cl.payload["v"]]
                    A.set_entry(row_i, iv, 1)
                    c_vec[row_i] = int(cl.payload["val"])
            return se.solve_torsor(A, c_vec, ring=self.ring, want_witness=False)

        res = build_and_solve(claims)
        ok = res.status in ("SAT_INTEGRAL", "SAT_Q")
        if ok:
            return True, res.status, None, None

        mus_ids: Optional[List[int]] = None
        if want_mus_on_fail:
            idx_list = list(range(len(claims)))

            def is_unsat(sub_idx: Sequence[int]) -> bool:
                r_s = build_and_solve([claims[i] for i in sub_idx])
                return r_s.status not in ("SAT_INTEGRAL", "SAT_Q")

            mus_rep = quickxplain_mus(idx_list, is_unsat, verify_minimality=True)
            mus_ids = [claims[i].claim_id for i in mus_rep.mus_ids]
        return False, res.status, res.torsion_cert, mus_ids

    def _eval_affine_1d(self, claim: FirewallClaim, mutate: bool) -> FirewallVerdict:
        t0 = time.perf_counter()
        u: int = int(claim.payload["u"])
        v: int = int(claim.payload["v"])
        cu: int = int(claim.payload["coeff_u"])
        cv: int = int(claim.payload["coeff_v"])
        rhs: int = int(claim.payload["rhs"])

        if cu == 0 or cv == 0:
            raise ValueError("affine_1d requires nonzero coeff_u and coeff_v")

        # Guardrail B 1-row GCD torsion check in O(1)!
        if self.ring == "Z":
            g_row = math.gcd(abs(cu), abs(cv))
            if g_row > 1 and rhs % g_row != 0:
                self.stats["fast_o1_hits"] += 1
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="FAST_REJECT_TORSION_O1",
                    reason=f"1-row GCD torsion: gcd({cu},{cv})={g_row} does not divide {rhs}",
                    contradiction_class="UNSAT_TORSION",
                    mus_claim_ids=[claim.claim_id],
                    torsion_cert=(g_row, rhs % g_row),
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )

        ru = self.comp_root.get(u, u)
        rv = self.comp_root.get(v, v)
        edge_is_unit = (abs(cu) == 1 and abs(cv) == 1)

        # ---- CASE 1: Tree-Edge Merge (ru != rv) ----
        if ru != rv:
            pin_u = self.comp_pinned.get(ru)
            pin_v = self.comp_pinned.get(rv)
            nonunit_u = self.comp_has_nonunit.get(ru, False)
            nonunit_v = self.comp_has_nonunit.get(rv, False)

            # Subcase 1a: Both components already pinned -> unique integral values verified at commit!
            if pin_u is not None and pin_v is not None:
                su, bu = self.pot_s.get(u, (1, 1)), self.pot_b.get(u, (0, 1))
                sv, bv = self.pot_s.get(v, (1, 1)), self.pot_b.get(v, (0, 1))
                xu = _radd(_rmul(su, pin_u), bu)
                xv = _radd(_rmul(sv, pin_v), bv)
                lhs = _rsub(_rmul((cv, 1), xv), _rmul((cu, 1), xu))
                if lhs != (rhs, 1):
                    self.stats["fast_o1_hits"] += 1
                    mus_list = [claim.claim_id]
                    if self.comp_pin_claim.get(ru) is not None:
                        mus_list.append(self.comp_pin_claim[ru])  # type: ignore[arg-type]
                    if self.comp_pin_claim.get(rv) is not None:
                        mus_list.append(self.comp_pin_claim[rv])  # type: ignore[arg-type]
                    return FirewallVerdict(
                        claim_id=claim.claim_id,
                        accepted=False,
                        path_taken="FAST_REJECT_FREE_O1",
                        reason="Pinned component mismatch on cross-edge",
                        contradiction_class="UNSAT_FREE_COHOMOLOGY",
                        mus_claim_ids=mus_list,
                        latency_us=(time.perf_counter() - t0) * 1e6,
                    )
                # Unique solutions in both pinned components are already integral & satisfy new edge!
                self.stats["fast_o1_hits"] += 1
                if mutate:
                    self._ensure_vertex_1d(u)
                    self._ensure_vertex_1d(v)
                    self._merge_forest_components(ru, rv, u, v, cu, cv, rhs, claim.claim_id)
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=True,
                    path_taken="FAST_TREE_MERGE_O1",
                    reason="O(1) verified pinned-to-pinned tree merge",
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )

            # Subcase 1b: Over Z, check exact sufficient condition for guaranteed O(1) integral merge:
            # - If neither pinned: one side has |coeff| == 1 and is pure unit-scale (so any Z-solution
            #   on the other side extends integrally across the edge to the entire unit-scale tree!).
            # - If exactly one side is pinned: the UNPINNED side has |coeff| == 1 and is pure unit-scale.
            can_fast_merge_z = False
            if self.ring == "Q":
                can_fast_merge_z = True
            elif pin_u is None and pin_v is None:
                can_fast_merge_z = (
                    (abs(cu) == 1 and not nonunit_u) or (abs(cv) == 1 and not nonunit_v)
                )
            elif pin_u is not None and pin_v is None:
                can_fast_merge_z = (abs(cv) == 1 and not nonunit_v)
            elif pin_v is not None and pin_u is None:
                can_fast_merge_z = (abs(cu) == 1 and not nonunit_u)

            if not can_fast_merge_z:
                self.stats["escalated_solves"] += 1
                merged_ids = self.comp_claims.get(ru, []) + self.comp_claims.get(rv, [])
                ok, st, tcert, mus = self._solve_1d_component_exact(merged_ids, extra_claim=claim)
                if not ok:
                    return FirewallVerdict(
                        claim_id=claim.claim_id,
                        accepted=False,
                        path_taken="ESCALATED_COMPONENT_EXACT",
                        reason=f"Localized component Z-torsor rejected merge ({st})",
                        contradiction_class=st,
                        mus_claim_ids=mus,
                        torsion_cert=tcert,
                        latency_us=(time.perf_counter() - t0) * 1e6,
                    )
                if mutate:
                    self._ensure_vertex_1d(u)
                    self._ensure_vertex_1d(v)
                    self._merge_forest_components(ru, rv, u, v, cu, cv, rhs, claim.claim_id)
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=True,
                    path_taken="ESCALATED_COMPONENT_EXACT",
                    reason="Verified non-unit tree merge via localized exact Z-solver",
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )

            # Pure O(log V) small-to-large tree merge with ZERO matrix solves!
            self.stats["fast_o1_hits"] += 1
            if mutate:
                self._ensure_vertex_1d(u)
                self._ensure_vertex_1d(v)
                self._merge_forest_components(ru, rv, u, v, cu, cv, rhs, claim.claim_id)
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=True,
                path_taken="FAST_TREE_MERGE_O1",
                reason="O(1) spanning-forest tree merge (0 matrix solves)",
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        # ---- CASE 2: Cycle Closure (ru == rv) ----
        r = ru
        su, bu = self.pot_s.get(u, (1, 1)), self.pot_b.get(u, (0, 1))
        sv, bv = self.pot_s.get(v, (1, 1)), self.pot_b.get(v, (0, 1))

        # Equation: cv*(sv*x_r + bv) - cu*(su*x_r + bu) = rhs
        #   ==> A_rat * x_r = B_rat
        A_rat = _rsub(_rmul((cv, 1), sv), _rmul((cu, 1), su))
        B_rat = _rsub((rhs, 1), _rsub(_rmul((cv, 1), bv), _rmul((cu, 1), bu)))
        pin_r = self.comp_pinned.get(r)
        nonunit_r = self.comp_has_nonunit.get(r, False)

        # Subcase 2a: Commuting Holonomy (A_rat == 0)
        if A_rat[0] == 0:
            if B_rat[0] != 0:
                self.stats["fast_o1_hits"] += 1
                mus = self._tree_path_claims(u, v) + [claim.claim_id]
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="FAST_REJECT_FREE_O1",
                    reason=f"O(1) commuting holonomy defect ({B_rat[0]}/{B_rat[1]} != 0)",
                    contradiction_class="UNSAT_FREE_COHOMOLOGY",
                    mus_claim_ids=mus,
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )
            # B_rat == 0: Exact Q-linear consequence of already-committed tree edges ->
            # holds identically for EVERY existing integral/rational solution (Guardrail A)!
            self.stats["fast_o1_hits"] += 1
            if mutate:
                self._ensure_vertex_1d(u)
                self._ensure_vertex_1d(v)
                self.comp_claims[r].append(claim.claim_id)
                if not edge_is_unit:
                    self.comp_has_nonunit[r] = True
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=True,
                path_taken="FAST_CORROBORATE_O1",
                reason="O(1) exact commuting corroboration (residual == 0, 0 matrix solves)",
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        # Subcase 2b: Gauge-Tightening Holonomy (A_rat != 0) ==> pins x_r = B_rat / A_rat!
        xr_req = _rdiv(B_rat, A_rat)
        if pin_r is not None:
            if xr_req != pin_r:
                self.stats["fast_o1_hits"] += 1
                mus = self._tree_path_claims(u, v) + [claim.claim_id]
                if self.comp_pin_claim.get(r) is not None and self.comp_pin_claim[r] not in mus:
                    mus.append(self.comp_pin_claim[r])  # type: ignore[arg-type]
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="FAST_REJECT_FREE_O1",
                    reason=f"O(1) gauge pin conflict: required {xr_req} != pinned {pin_r}",
                    contradiction_class="UNSAT_FREE_COHOMOLOGY",
                    mus_claim_ids=mus,
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )
            # Already pinned to xr_req & verified integral -> O(1) exact corroboration!
            self.stats["fast_o1_hits"] += 1
            if mutate:
                self._ensure_vertex_1d(u)
                self._ensure_vertex_1d(v)
                self.comp_claims[r].append(claim.claim_id)
                if not edge_is_unit:
                    self.comp_has_nonunit[r] = True
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=True,
                path_taken="FAST_CORROBORATE_O1",
                reason="O(1) corroborated existing gauge pin",
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        # Unpinned component over Q: any xr_req is valid!
        if self.ring == "Q":
            self.stats["fast_o1_hits"] += 1
            if mutate:
                self._ensure_vertex_1d(u)
                self._ensure_vertex_1d(v)
                self.comp_pinned[r] = xr_req
                self.comp_pin_claim[r] = claim.claim_id
                self.comp_claims[r].append(claim.claim_id)
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=True,
                path_taken="FAST_GAUGE_PIN_O1",
                reason=f"O(1) exact Q gauge pin x_root = {xr_req[0]}/{xr_req[1]}",
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        # Unpinned component over Z with pure unit-scale edges: x_r integral <=> ALL vertices integral!
        if (not nonunit_r) and edge_is_unit:
            if xr_req[1] != 1:
                self.stats["fast_o1_hits"] += 1
                mus = self._tree_path_claims(u, v) + [claim.claim_id]
                mod_m = xr_req[1]
                rem_m = xr_req[0] % mod_m
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="FAST_REJECT_TORSION_O1",
                    reason=f"O(1) unit-scale torsion obstruction: x_root = {xr_req[0]}/{mod_m} not in Z",
                    contradiction_class="UNSAT_TORSION",
                    mus_claim_ids=mus,
                    torsion_cert=(mod_m, rem_m),
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )
            self.stats["fast_o1_hits"] += 1
            if mutate:
                self._ensure_vertex_1d(u)
                self._ensure_vertex_1d(v)
                self.comp_pinned[r] = xr_req
                self.comp_pin_claim[r] = claim.claim_id
                self.comp_claims[r].append(claim.claim_id)
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=True,
                path_taken="FAST_GAUGE_PIN_O1",
                reason=f"O(1) exact integral gauge pin x_root = {xr_req[0]}",
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        # Unpinned non-unit component over Z (e.g., stealth {-2,-1,0,1,2} scale-trap closing edge!):
        # Since every vertex w in r satisfies x_w = s_w * xr_req + b_w uniquely,
        # the component is integrally satisfiable IFF EVERY vertex w has integral value!
        bad_v: Optional[int] = None
        bad_val: Rat = (0, 1)
        for w in self.comp_members.get(r, [u]):
            val_w = _radd(_rmul(self.pot_s.get(w, (1, 1)), xr_req), self.pot_b.get(w, (0, 1)))
            if val_w[1] != 1:
                bad_v = w
                bad_val = val_w
                break

        if bad_v is not None:
            path_cids = self._tree_path_claims(u, v)
            fast_cert = self._is_provably_minimal_cycle_mus(u, v, claim, path_cids, xr_req)
            if fast_cert is not None:
                self.stats["fast_o1_hits"] += 1
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="FAST_REJECT_TORSION_O1",
                    reason=f"O(L) exact scale/torsion cycle obstruction: mod {fast_cert[0]} != 0 (rem {fast_cert[1]})",
                    contradiction_class="UNSAT_TORSION",
                    mus_claim_ids=path_cids + [claim.claim_id],
                    torsion_cert=fast_cert,
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )

            self.stats["escalated_solves"] += 1
            # Fallback: extract minimal MUS via localized exact Z-solver if component is moderate
            comp_cids = self.comp_claims.get(r, [])
            if len(comp_cids) <= 250:
                _, st, tcert, mus = self._solve_1d_component_exact(comp_cids, extra_claim=claim)
                tcert_final = tcert if tcert is not None else (bad_val[1], bad_val[0] % bad_val[1])
            else:
                st = "UNSAT_TORSION"
                tcert_final = (bad_val[1], bad_val[0] % bad_val[1])
                mus = path_cids + [claim.claim_id]
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=False,
                path_taken="ESCALATED_COMPONENT_EXACT",
                reason=f"Non-unit scale/torsion obstruction at v={bad_v}: x_v={bad_val[0]}/{bad_val[1]} not in Z",
                contradiction_class=st,
                mus_claim_ids=mus,
                torsion_cert=tcert_final,
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        self.stats["escalated_solves"] += 1
        if mutate:
            self._ensure_vertex_1d(u)
            self._ensure_vertex_1d(v)
            self.comp_pinned[r] = xr_req
            self.comp_pin_claim[r] = claim.claim_id
            self.comp_claims[r].append(claim.claim_id)
            self.comp_has_nonunit[r] = True
        return FirewallVerdict(
            claim_id=claim.claim_id,
            accepted=True,
            path_taken="ESCALATED_COMPONENT_EXACT",
            reason="Verified non-unit integral gauge pin across all component vertices",
            latency_us=(time.perf_counter() - t0) * 1e6,
        )

    def _merge_forest_components(
        self, ru: int, rv: int, u: int, v: int, cu: int, cv: int, rhs: int, claim_id: int
    ) -> None:
        """Small-to-large merge of spanning-forest components ru and rv."""
        # Always absorb smaller component into larger component (O(log V) amortized!)
        if len(self.comp_members[ru]) < len(self.comp_members[rv]):
            # Flip equation: (-cu)*x_u - (-cv)*x_v = rhs -> swap u/v so rv is absorbed into ru!
            ru, rv = rv, ru
            u, v = v, u
            cu, cv = -cv, -cu

        # Now rv is absorbed into ru. Express x_{rv} in terms of x_{ru}:
        # cv*(sv*x_{rv} + bv) - cu*(su*x_{ru} + bu) = rhs
        # ==> x_{rv} = alpha * x_{ru} + beta
        su, bu = self.pot_s[u], self.pot_b[u]
        sv, bv = self.pot_s[v], self.pot_b[v]
        denom = _rmul((cv, 1), sv)
        alpha = _rdiv(_rmul((cu, 1), su), denom)
        num_beta = _rsub(_radd((rhs, 1), _rmul((cu, 1), bu)), _rmul((cv, 1), bv))
        beta = _rdiv(num_beta, denom)

        # Update all vertices w in rv: x_w = sw*(alpha*x_{ru} + beta) + bw
        for w in self.comp_members[rv]:
            sw, bw = self.pot_s[w], self.pot_b[w]
            self.pot_s[w] = _rmul(sw, alpha)
            self.pot_b[w] = _radd(_rmul(sw, beta), bw)
            self.comp_root[w] = ru

        self.comp_members[ru].extend(self.comp_members.pop(rv))
        pin_v = self.comp_pinned.pop(rv)
        pin_claim_v = self.comp_pin_claim.pop(rv)
        if self.comp_pinned[ru] is None and pin_v is not None:
            # pin_v = alpha * x_{ru} + beta ==> x_{ru} = (pin_v - beta) / alpha
            self.comp_pinned[ru] = _rdiv(_rsub(pin_v, beta), alpha)
            self.comp_pin_claim[ru] = pin_claim_v

        nonunit_v = self.comp_has_nonunit.pop(rv)
        if nonunit_v or abs(cu) != 1 or abs(cv) != 1:
            self.comp_has_nonunit[ru] = True

        self.comp_claims[ru].extend(self.comp_claims.pop(rv))
        self.comp_claims[ru].append(claim_id)
        self.tree_adj[u].append((v, claim_id))
        self.tree_adj[v].append((u, claim_id))

    def _eval_anchor_1d(self, claim: FirewallClaim, mutate: bool) -> FirewallVerdict:
        t0 = time.perf_counter()
        v = int(claim.payload["v"])
        val = int(claim.payload["val"])
        r = self.comp_root.get(v, v)
        sv, bv = self.pot_s.get(v, (1, 1)), self.pot_b.get(v, (0, 1))
        # sv * x_r + bv = val ==> x_r = (val - bv) / sv
        xr_req = _rdiv(_rsub((val, 1), bv), sv)
        pin_r = self.comp_pinned.get(r)
        if pin_r is not None:
            if pin_r != xr_req:
                self.stats["fast_o1_hits"] += 1
                mus = [claim.claim_id]
                if self.comp_pin_claim.get(r) is not None:
                    mus.append(self.comp_pin_claim[r])  # type: ignore[arg-type]
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="FAST_REJECT_FREE_O1",
                    reason=f"Anchor conflict: x_{v}={val} implies x_root={xr_req} != pinned {pin_r}",
                    contradiction_class="UNSAT_FREE_COHOMOLOGY",
                    mus_claim_ids=mus,
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )
            self.stats["fast_o1_hits"] += 1
            if mutate:
                self._ensure_vertex_1d(v)
                self.comp_claims[r].append(claim.claim_id)
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=True,
                path_taken="FAST_CORROBORATE_O1",
                reason=f"O(1) corroborated existing gauge pin via anchor x_{v} = {val}",
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        if self.ring == "Z" and self.comp_has_nonunit.get(r, False):
            bad_v: Optional[int] = None
            bad_val: Rat = (0, 1)
            for w in self.comp_members.get(r, [v]):
                val_w = _radd(_rmul(self.pot_s.get(w, (1, 1)), xr_req), self.pot_b.get(w, (0, 1)))
                if val_w[1] != 1:
                    bad_v = w
                    bad_val = val_w
                    break
            if bad_v is not None:
                self.stats["escalated_solves"] += 1
                _, st, tcert, mus = self._solve_1d_component_exact(
                    self.comp_claims.get(r, []), extra_claim=claim
                )
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="ESCALATED_COMPONENT_EXACT",
                    reason=f"Anchor rejected on non-unit Z component at v={bad_v}: {bad_val}",
                    contradiction_class=st,
                    mus_claim_ids=mus,
                    torsion_cert=tcert if tcert is not None else (bad_val[1], bad_val[0] % bad_val[1]),
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )
        elif self.ring == "Z" and xr_req[1] != 1:
            self.stats["fast_o1_hits"] += 1
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=False,
                path_taken="FAST_REJECT_TORSION_O1",
                reason=f"Anchor implies non-integral root {xr_req}",
                contradiction_class="UNSAT_TORSION",
                mus_claim_ids=[claim.claim_id],
                torsion_cert=(xr_req[1], xr_req[0] % xr_req[1]),
                latency_us=(time.perf_counter() - t0) * 1e6,
            )

        self.stats["fast_o1_hits"] += 1
        if mutate:
            self._ensure_vertex_1d(v)
            self.comp_pinned[r] = xr_req
            self.comp_pin_claim[r] = claim.claim_id
            self.comp_claims[r].append(claim.claim_id)
        return FirewallVerdict(
            claim_id=claim.claim_id,
            accepted=True,
            path_taken="FAST_GAUGE_PIN_O1",
            reason=f"Pinned anchor x_{v} = {val}",
            latency_us=(time.perf_counter() - t0) * 1e6,
        )

    def _eval_vector_q(self, claim: FirewallClaim, mutate: bool) -> FirewallVerdict:
        """Exact Q multi-stalk vector claim (e.g. non-dyadic Hilbert/Cauchy updates -> 0 FP!)."""
        t0 = time.perf_counter()
        self.stats["escalated_solves"] += 1
        grp = str(claim.payload.get("group", "default"))
        all_cl = self.vec_groups.get(grp, []) + [claim]

        # Build exact rational row-LCM cleared SparseIntMatrix
        n_cols = max(cl.payload["n_cols"] for cl in all_cl)
        rat_entries: List[Tuple[int, int, int, int]] = []
        rat_rhs: List[Rat] = []
        r_cur = 0
        for cl in all_cl:
            for row_entries, rhs_rat in cl.payload["rows"]:
                for col_j, num, den in row_entries:
                    rat_entries.append((r_cur, col_j, num, den))
                rat_rhs.append(rhs_rat)
                r_cur += 1
        A_q, c_q = se.SparseIntMatrix.from_rational_rows(r_cur, n_cols, rat_entries, rat_rhs)
        res = se.solve_torsor(A_q, c_q, ring="Q", want_witness=False)
        if res.status != "SAT_Q":
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=False,
                path_taken="VECTOR_Q_EXACT",
                reason="Exact Q multi-stalk contradiction",
                contradiction_class="UNSAT_FREE_COHOMOLOGY",
                mus_claim_ids=[cl.claim_id for cl in all_cl],
                latency_us=(time.perf_counter() - t0) * 1e6,
            )
        if mutate:
            self.vec_groups.setdefault(grp, []).append(claim)
        return FirewallVerdict(
            claim_id=claim.claim_id,
            accepted=True,
            path_taken="VECTOR_Q_EXACT",
            reason="Verified exact Q multi-stalk update (zero float rounding error)",
            latency_us=(time.perf_counter() - t0) * 1e6,
        )

    def _eval_simplex_h2(self, claim: FirewallClaim, mutate: bool) -> FirewallVerdict:
        """Exact Z simplicial 2-simplex H^2 claim (delta^1 y = d)."""
        t0 = time.perf_counter()
        self.stats["escalated_solves"] += 1
        grp = str(claim.payload.get("group", "default"))
        all_cl = [cl for cl in self.h2_claims if str(cl.payload.get("group", "default")) == grp] + [claim]

        def solve_faces(sub_cl: Sequence[FirewallClaim]) -> se.TorsorResult:
            edge_map: Dict[Tuple[int, int], int] = {}
            D1 = se.SparseIntMatrix(len(sub_cl), len(sub_cl) * 3)
            d_vec = [0] * len(sub_cl)
            for row_i, cl in enumerate(sub_cl):
                u, v, w = int(cl.payload["u"]), int(cl.payload["v"]), int(cl.payload["w"])
                verts = [u, v, w]
                inv = sum(1 for i in range(3) for j in range(i + 1, 3) if verts[i] > verts[j])
                orient = -1 if (inv & 1) else 1
                a, b, c_v = sorted(verts)
                for (p1, p2), sgn in (((b, c_v), orient), ((a, c_v), -orient), ((a, b), orient)):
                    ek = (p1, p2)
                    eid = edge_map.get(ek)
                    if eid is None:
                        eid = len(edge_map)
                        edge_map[ek] = eid
                    D1.add_entry(row_i, eid, sgn)
                d_vec[row_i] = int(cl.payload["rhs"])
            D1.ncols = len(edge_map)
            return se.solve_torsor(D1, d_vec, ring="Z", want_witness=False)

        res = solve_faces(all_cl)
        if res.status != "SAT_INTEGRAL":
            idx_all = list(range(len(all_cl)))
            mus_rep = quickxplain_mus(
                idx_all,
                lambda sub: solve_faces([all_cl[i] for i in sub]).status != "SAT_INTEGRAL",
                verify_minimality=True,
            )
            mus_ids = [all_cl[i].claim_id for i in mus_rep.mus_ids]
            return FirewallVerdict(
                claim_id=claim.claim_id,
                accepted=False,
                path_taken="H2_SIMPLEX_EXACT",
                reason=f"Exact Z H^2 multi-premise obstruction ({res.status})",
                contradiction_class=res.status,
                mus_claim_ids=mus_ids,
                torsion_cert=res.torsion_cert,
                latency_us=(time.perf_counter() - t0) * 1e6,
            )
        if mutate:
            self.h2_claims.append(claim)
        return FirewallVerdict(
            claim_id=claim.claim_id,
            accepted=True,
            path_taken="H2_SIMPLEX_EXACT",
            reason="Verified exact Z H^2 2-simplex constraint",
            latency_us=(time.perf_counter() - t0) * 1e6,
        )

    def _eval_tarski(self, claim: FirewallClaim, mutate: bool) -> FirewallVerdict:
        """Incremental Lawvere-Tarski dirty-queue SPFA/BFS bound propagation (x_u + offset <= x_v)
        with O(V+E) positive-offset cycle detection & cycle MUS extraction."""
        t0 = time.perf_counter()
        self.stats["fast_o1_hits"] += 1
        # Copy-on-write delta dicts so rejected proposals touch ZERO committed state!
        lo_delta: Dict[int, int] = {}
        hi_delta: Dict[int, int] = {}

        def get_lo(x: int) -> int:
            return lo_delta.get(x, self.tarski_lo.get(x, -10**9))

        def get_hi(x: int) -> int:
            return hi_delta.get(x, self.tarski_hi.get(x, 10**9))

        extra_out: Dict[int, List[Tuple[int, int, int]]] = {}
        extra_in: Dict[int, List[Tuple[int, int, int]]] = {}
        q_lo: deque = deque()
        q_hi: deque = deque()
        known_nodes: Set[int] = set(self.tarski_lo) | set(self.tarski_hi) | set(self.tarski_out) | set(self.tarski_in)

        if claim.kind == "tarski_bound":
            v = int(claim.payload["v"])
            known_nodes.add(v)
            nl = max(get_lo(v), int(claim.payload["lo"]))
            nh = min(get_hi(v), int(claim.payload["hi"]))
            if nl > nh:
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="TARSKI_INCREMENTAL_BFS",
                    reason=f"Tarski bound contradiction on v={v}: [{nl}, {nh}]",
                    contradiction_class="UNSAT_TARSKI_ORDER",
                    mus_claim_ids=[claim.claim_id],
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )
            if nl > get_lo(v):
                lo_delta[v] = nl
                q_lo.append(v)
            if nh < get_hi(v):
                hi_delta[v] = nh
                q_hi.append(v)
        else:
            u = int(claim.payload["u"])
            v = int(claim.payload["v"])
            off = int(claim.payload.get("offset", 0))
            if u == v and off > 0:
                return FirewallVerdict(
                    claim_id=claim.claim_id,
                    accepted=False,
                    path_taken="TARSKI_INCREMENTAL_BFS",
                    reason=f"Tarski strict self-loop contradiction: x_{u} + {off} <= x_{u}",
                    contradiction_class="UNSAT_TARSKI_ORDER",
                    mus_claim_ids=[claim.claim_id],
                    latency_us=(time.perf_counter() - t0) * 1e6,
                )
            known_nodes.add(u)
            known_nodes.add(v)
            extra_out.setdefault(u, []).append((v, off, claim.claim_id))
            extra_in.setdefault(v, []).append((u, off, claim.claim_id))
            q_lo.append(u)
            q_hi.append(v)

        max_relax = max(len(known_nodes) + 1, 2)
        relax_lo: Dict[int, int] = {}
        relax_hi: Dict[int, int] = {}
        pred_lo: Dict[int, Tuple[int, int]] = {}  # v -> (u, claim_id)
        pred_hi: Dict[int, Tuple[int, int]] = {}  # u -> (v, claim_id)

        def extract_cycle_mus(start: int, preds: Dict[int, Tuple[int, int]]) -> List[int]:
            seen_pos: Dict[int, int] = {}
            chain_nodes: List[int] = []
            chain_cids: List[int] = []
            cur = start
            while cur in preds and cur not in seen_pos:
                seen_pos[cur] = len(chain_nodes)
                chain_nodes.append(cur)
                prev, cid = preds[cur]
                chain_cids.append(cid)
                cur = prev
            if cur in seen_pos:
                idx0 = seen_pos[cur]
                cyc = list(dict.fromkeys(chain_cids[idx0:]))
                if claim.claim_id not in cyc:
                    cyc.append(claim.claim_id)
                return cyc
            return [claim.claim_id]

        # Incremental SPFA/BFS tightening with positive-offset cycle guard
        while q_lo or q_hi:
            while q_lo:
                u_cur = q_lo.popleft()
                lu = get_lo(u_cur)
                nbrs = list(self.tarski_out.get(u_cur, ())) + extra_out.get(u_cur, [])
                for v2, off2, cid2 in nbrs:
                    cand = lu + off2
                    if cand > get_lo(v2):
                        pred_lo[v2] = (u_cur, cid2)
                        rc = relax_lo.get(v2, 0) + 1
                        relax_lo[v2] = rc
                        if rc > max_relax:
                            return FirewallVerdict(
                                claim_id=claim.claim_id,
                                accepted=False,
                                path_taken="TARSKI_INCREMENTAL_BFS",
                                reason=f"Tarski positive-offset directed cycle detected at v={v2}",
                                contradiction_class="UNSAT_TARSKI_ORDER",
                                mus_claim_ids=extract_cycle_mus(v2, pred_lo),
                                latency_us=(time.perf_counter() - t0) * 1e6,
                            )
                        if cand > get_hi(v2):
                            return FirewallVerdict(
                                claim_id=claim.claim_id,
                                accepted=False,
                                path_taken="TARSKI_INCREMENTAL_BFS",
                                reason=f"Tarski forward propagation conflict at v={v2}: lo={cand} > hi={get_hi(v2)}",
                                contradiction_class="UNSAT_TARSKI_ORDER",
                                mus_claim_ids=[claim.claim_id],
                                latency_us=(time.perf_counter() - t0) * 1e6,
                            )
                        lo_delta[v2] = cand
                        q_lo.append(v2)
            while q_hi:
                v_cur = q_hi.popleft()
                hv = get_hi(v_cur)
                preds = list(self.tarski_in.get(v_cur, ())) + extra_in.get(v_cur, [])
                for u2, off2, cid2 in preds:
                    cand = hv - off2
                    if cand < get_hi(u2):
                        pred_hi[u2] = (v_cur, cid2)
                        rc = relax_hi.get(u2, 0) + 1
                        relax_hi[u2] = rc
                        if rc > max_relax:
                            return FirewallVerdict(
                                claim_id=claim.claim_id,
                                accepted=False,
                                path_taken="TARSKI_INCREMENTAL_BFS",
                                reason=f"Tarski positive-offset directed cycle detected (backward) at u={u2}",
                                contradiction_class="UNSAT_TARSKI_ORDER",
                                mus_claim_ids=extract_cycle_mus(u2, pred_hi),
                                latency_us=(time.perf_counter() - t0) * 1e6,
                            )
                        if cand < get_lo(u2):
                            return FirewallVerdict(
                                claim_id=claim.claim_id,
                                accepted=False,
                                path_taken="TARSKI_INCREMENTAL_BFS",
                                reason=f"Tarski backward Modus Tollens conflict at u={u2}: hi={cand} < lo={get_lo(u2)}",
                                contradiction_class="UNSAT_TARSKI_ORDER",
                                mus_claim_ids=[claim.claim_id],
                                latency_us=(time.perf_counter() - t0) * 1e6,
                            )
                        hi_delta[u2] = cand
                        q_hi.append(u2)

        if mutate:
            self.tarski_lo.update(lo_delta)
            self.tarski_hi.update(hi_delta)
            if claim.kind == "tarski_order":
                u, v = int(claim.payload["u"]), int(claim.payload["v"])
                off = int(claim.payload.get("offset", 0))
                self.tarski_out.setdefault(u, []).append((v, off, claim.claim_id))
                self.tarski_in.setdefault(v, []).append((u, off, claim.claim_id))
            self.tarski_claims.append(claim)

        return FirewallVerdict(
            claim_id=claim.claim_id,
            accepted=True,
            path_taken="TARSKI_INCREMENTAL_BFS",
            reason="Verified incremental Tarski order fixpoint",
            latency_us=(time.perf_counter() - t0) * 1e6,
        )

    def propose_claim(self, claim: FirewallClaim) -> FirewallVerdict:
        """Evaluate a claim transactionally WITHOUT mutating committed state."""
        self.stats["total_proposed"] += 1
        if claim.kind == "affine_1d":
            return self._eval_affine_1d(claim, mutate=False)
        if claim.kind == "anchor_1d":
            return self._eval_anchor_1d(claim, mutate=False)
        if claim.kind == "vector_q":
            return self._eval_vector_q(claim, mutate=False)
        if claim.kind == "simplex_h2":
            return self._eval_simplex_h2(claim, mutate=False)
        if claim.kind in ("tarski_order", "tarski_bound"):
            return self._eval_tarski(claim, mutate=False)
        raise ValueError(f"Unknown claim kind {claim.kind!r}")

    def commit_claim(self, claim: FirewallClaim) -> FirewallVerdict:
        """Verify claim and commit iff 100% consistent; otherwise quarantine before commit!"""
        self.stats["total_proposed"] += 1
        if claim.kind == "affine_1d":
            verdict = self._eval_affine_1d(claim, mutate=True)
        elif claim.kind == "anchor_1d":
            verdict = self._eval_anchor_1d(claim, mutate=True)
        elif claim.kind == "vector_q":
            verdict = self._eval_vector_q(claim, mutate=True)
        elif claim.kind == "simplex_h2":
            verdict = self._eval_simplex_h2(claim, mutate=True)
        elif claim.kind in ("tarski_order", "tarski_bound"):
            verdict = self._eval_tarski(claim, mutate=True)
        else:
            raise ValueError(f"Unknown claim kind {claim.kind!r}")

        if verdict.accepted:
            self.committed_claims.append(claim)
            self.claim_by_id[claim.claim_id] = claim
            self.stats["total_committed"] += 1
        else:
            self.quarantine.append((claim, verdict))
            self.stats["total_quarantined"] += 1
        return verdict

    def checkpoint(self) -> int:
        """Create a lightweight transactional checkpoint returning its integer ID."""
        cid = self._next_ckpt_id
        self._next_ckpt_id += 1
        self.checkpoints[cid] = len(self.committed_claims)
        return cid

    def rollback(self, checkpoint_id: int) -> None:
        """Roll back committed memory cleanly to the exact state at `checkpoint_id`."""
        if checkpoint_id not in self.checkpoints:
            raise KeyError(f"Unknown checkpoint_id {checkpoint_id}")
        target_len = self.checkpoints[checkpoint_id]
        kept = list(self.committed_claims[:target_len])
        # Cleanly rebuild in-memory indices by replaying the verified committed prefix!
        saved_ckpts = {k: v for k, v in self.checkpoints.items() if v <= target_len}
        saved_next = self._next_ckpt_id
        self.__init__(ring=self.ring)  # type: ignore[misc]
        self.checkpoints = saved_ckpts
        self._next_ckpt_id = saved_next
        for cl in kept:
            v = self.commit_claim(cl)
            assert v.accepted, f"Internal rollback invariant failed on claim {cl.claim_id}"

    def verify_committed_state_from_scratch(self) -> Tuple[bool, str]:
        """Clean-Room Batch Audit: independently solves EVERY committed lane from scratch
        and verifies exact witnesses to certify 100.0% transactional integrity!
        """
        # 1. Verify ALL 1D affine & anchor claims jointly over self.ring!
        c1d = [cl for cl in self.committed_claims if cl.kind in ("affine_1d", "anchor_1d")]
        if c1d:
            verts: Dict[int, int] = {}
            for cl in c1d:
                if cl.kind == "affine_1d":
                    verts.setdefault(int(cl.payload["u"]), len(verts))
                    verts.setdefault(int(cl.payload["v"]), len(verts))
                else:
                    verts.setdefault(int(cl.payload["v"]), len(verts))
            A = se.SparseIntMatrix(len(c1d), len(verts))
            c_vec = [0] * len(c1d)
            for idx, cl in enumerate(c1d):
                if cl.kind == "affine_1d":
                    A.add_entry(idx, verts[int(cl.payload["u"])], -int(cl.payload["coeff_u"]))
                    A.add_entry(idx, verts[int(cl.payload["v"])], int(cl.payload["coeff_v"]))
                    c_vec[idx] = int(cl.payload["rhs"])
                else:
                    A.set_entry(idx, verts[int(cl.payload["v"])], 1)
                    c_vec[idx] = int(cl.payload["val"])
            res = se.solve_torsor(A, c_vec, ring=self.ring, want_witness=True)
            ok_c, msg_c = se.verify_torsor_certificate(A, c_vec, res)
            if res.status not in ("SAT_INTEGRAL", "SAT_Q") or not ok_c:
                return False, f"1D batch audit FAILED: {res.status} / {msg_c}"

        # 2. Verify ALL Vector Q groups
        for grp, cls in self.vec_groups.items():
            n_cols = max(cl.payload["n_cols"] for cl in cls)
            rat_entries, rat_rhs, r_cur = [], [], 0
            for cl in cls:
                for row_entries, rhs_rat in cl.payload["rows"]:
                    for col_j, num, den in row_entries:
                        rat_entries.append((r_cur, col_j, num, den))
                    rat_rhs.append(rhs_rat)
                    r_cur += 1
            Aq, cq = se.SparseIntMatrix.from_rational_rows(r_cur, n_cols, rat_entries, rat_rhs)
            rq = se.solve_torsor(Aq, cq, ring="Q", want_witness=True)
            if rq.status != "SAT_Q" or not se.verify_torsor_certificate(Aq, cq, rq)[0]:
                return False, f"Vector Q group {grp} batch audit FAILED"

        # 3. Verify ALL H^2 simplex groups
        h2_by_grp: Dict[str, List[FirewallClaim]] = {}
        for cl in self.h2_claims:
            h2_by_grp.setdefault(str(cl.payload.get("group", "default")), []).append(cl)
        for grp, cls in h2_by_grp.items():
            edge_map: Dict[Tuple[int, int], int] = {}
            D1 = se.SparseIntMatrix(len(cls), len(cls) * 3)
            d_vec = [0] * len(cls)
            for row_i, cl in enumerate(cls):
                u, v, w = int(cl.payload["u"]), int(cl.payload["v"]), int(cl.payload["w"])
                verts = [u, v, w]
                inv = sum(1 for i in range(3) for j in range(i + 1, 3) if verts[i] > verts[j])
                orient = -1 if (inv & 1) else 1
                a, b, c_v = sorted(verts)
                for (p1, p2), sgn in (((b, c_v), orient), ((a, c_v), -orient), ((a, b), orient)):
                    eid = edge_map.setdefault((p1, p2), len(edge_map))
                    D1.add_entry(row_i, eid, sgn)
                d_vec[row_i] = int(cl.payload["rhs"])
            D1.ncols = len(edge_map)
            r_h2 = se.solve_torsor(D1, d_vec, ring="Z", want_witness=True)
            if r_h2.status != "SAT_INTEGRAL" or not se.verify_torsor_certificate(D1, d_vec, r_h2)[0]:
                return False, f"H^2 group {grp} batch audit FAILED"

        # 4. Verify Tarski bounds & order edges explicitly against witness x_v = tarski_lo[v]
        t_nodes: Set[int] = set(self.tarski_lo) | set(self.tarski_hi) | set(self.tarski_out) | set(self.tarski_in)
        for v in t_nodes:
            lo_v = self.tarski_lo.get(v, -10**9)
            hi_v = self.tarski_hi.get(v, 10**9)
            if lo_v > hi_v:
                return False, f"Tarski batch audit FAILED at v={v}: lo={lo_v} > hi={hi_v}"
        for cl in self.tarski_claims:
            if cl.kind == "tarski_bound":
                v = int(cl.payload["v"])
                xv = self.tarski_lo.get(v, -10**9)
                if not (int(cl.payload["lo"]) <= xv <= int(cl.payload["hi"])):
                    return False, f"Tarski bound witness failed on claim {cl.claim_id}"
            elif cl.kind == "tarski_order":
                u, v = int(cl.payload["u"]), int(cl.payload["v"])
                off = int(cl.payload.get("offset", 0))
                xu = self.tarski_lo.get(u, -10**9)
                xv = self.tarski_lo.get(v, -10**9)
                if xu + off > xv:
                    return False, f"Tarski order witness failed on claim {cl.claim_id}: {xu}+{off} > {xv}"

        return True, (
            f"Clean-room batch audit CERTIFIED 100% consistent across {len(self.committed_claims)} committed claims "
            f"({len(c1d)} 1D, {len(self.vec_groups)} VecQ, {len(self.h2_claims)} H^2, {len(self.tarski_claims)} Tarski)"
        )
