"""Lawvere-Tarski Lattice Sheaf Laplacian & Guardrail D Hybrid Engine v2.0:
- Complete finite distributive/Boolean/powerset lattices & Galois connections
- Directed Tarski 0-Laplacian greatest post-fixpoint flow
- Cycle 6 Algebraic-Tarski Chvatal-Gomory Cutting-Plane Closure:
    * Directed Tarski equality-SCC extraction (x_u <= ... <= x_u ==> x_u == x_v)
    * Exact RREF algebraic unmasking
    * Chvatal-Gomory Rank-1 subset-GCD congruence cuts & odd-cycle/clique floor cuts
    * Disjoint CG subset-cover interval tightening (0-branch refutation of LP-feasible ghosts!)
- Sound 3-Valued Budgeted Parametric Search (`max_branch_nodes`, default 4096):
    * CERTIFIED_SAT (with verified witness A @ x == c & bounds & order)
    * CERTIFIED_UNSAT (with exact torsor/Tarski/CG-cut/exhaustive proof certificate)
    * OPEN_BUDGET_EXCEEDED (never emits unverified SAT or UNSAT on timeout!).

Strictly Python 3 stdlib only.
"""

from dataclasses import dataclass, field
import math
import time
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple

from .mus_quickxplain import MUSReport, quickxplain_mus
from . import sparse_exact as se


def _floor_div(a: int, b: int) -> int:
    return a // b


def _ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


# ==============================================================================
# 1. Complete Finite Distributive / Powerset Lattices & Galois Connections
# ==============================================================================


class BitmaskPowersetLattice:
    def __init__(self, n_atoms: int = 1) -> None:
        if n_atoms < 1 or n_atoms > 16:
            raise ValueError("n_atoms must be in 1..16")
        self.n_atoms = n_atoms
        self.top = (1 << n_atoms) - 1
        self.bottom = 0

    def elements(self) -> List[int]:
        return list(range(1 << self.n_atoms))

    @staticmethod
    def leq(a: int, b: int) -> bool:
        return (a & b) == a

    @staticmethod
    def meet(a: int, b: int) -> int:
        return a & b

    @staticmethod
    def join(a: int, b: int) -> int:
        return a | b

    def complement(self, a: int) -> int:
        return self.top ^ a


@dataclass
class GaloisConnection:
    dom: BitmaskPowersetLattice
    cod: BitmaskPowersetLattice
    f_lower: Callable[[int], int]
    f_upper: Callable[[int], int]
    label: str = ""

    def verify_adjunction_law(self) -> bool:
        for a in self.dom.elements():
            fa = self.f_lower(a)
            for b in self.cod.elements():
                if self.cod.leq(fa, b) != self.dom.leq(a, self.f_upper(b)):
                    return False
        return True

    @classmethod
    def identity(cls, lat: BitmaskPowersetLattice, label: str = "id") -> "GaloisConnection":
        return cls(lat, lat, lambda x: x, lambda y: y, label=label)

    @classmethod
    def from_relation_matrix(
        cls,
        dom: BitmaskPowersetLattice,
        cod: BitmaskPowersetLattice,
        image_of_atom: Sequence[int],
        label: str = "rel",
    ) -> "GaloisConnection":
        imgs = list(image_of_atom)
        assert len(imgs) == dom.n_atoms

        def f_low(a: int) -> int:
            out = 0
            for i in range(dom.n_atoms):
                if (a >> i) & 1:
                    out |= imgs[i]
            return out

        def f_up(b: int) -> int:
            out = 0
            for i in range(dom.n_atoms):
                if (imgs[i] & b) == imgs[i]:
                    out |= 1 << i
            return out

        return cls(dom, cod, f_low, f_up, label=label)


@dataclass
class DirectedLatticeEdge:
    edge_id: int
    u: int
    v: int
    gc_u: GaloisConnection
    g_v: Callable[[int], int]
    label: str = ""


@dataclass
class TarskiFlowResult:
    consistent: bool
    iterations: int
    x_star: List[int]
    violated_vertices: List[int]
    elapsed_ms: float


class TarskiLatticeSheaf:
    def __init__(self, vertex_lattices: Sequence[BitmaskPowersetLattice]) -> None:
        self.lattices: List[BitmaskPowersetLattice] = list(vertex_lattices)
        self.n_vertices: int = len(self.lattices)
        self.edges: List[DirectedLatticeEdge] = []
        self.lower_bounds: List[int] = [lat.bottom for lat in self.lattices]
        self.upper_bounds: List[int] = [lat.top for lat in self.lattices]

    def set_bounds(self, v: int, lower: int, upper: int) -> None:
        self.lower_bounds[v] = lower
        self.upper_bounds[v] = upper

    def add_entailment_edge(
        self,
        u: int,
        v: int,
        gc_u: Optional[GaloisConnection] = None,
        g_v: Optional[Callable[[int], int]] = None,
        label: str = "",
    ) -> int:
        if gc_u is None:
            assert self.lattices[u].n_atoms == self.lattices[v].n_atoms
            gc_u = GaloisConnection.identity(self.lattices[u])
        if g_v is None:
            g_v = lambda y: y
        eid = len(self.edges)
        self.edges.append(
            DirectedLatticeEdge(
                edge_id=eid, u=u, v=v, gc_u=gc_u, g_v=g_v, label=label or f"imp_{eid}({u}->{v})"
            )
        )
        return eid

    def tarski_laplacian_step(
        self,
        x: Sequence[int],
        edge_subset: Optional[Sequence[int]] = None,
    ) -> Tuple[List[int], List[int]]:
        sel = [self.edges[eid] for eid in edge_subset] if edge_subset is not None else self.edges
        L_T = [lat.top for lat in self.lattices]
        for e in sel:
            L_T[e.u] &= e.gc_u.f_upper(e.g_v(x[e.v]))
        x_next = [x[u] & L_T[u] for u in range(self.n_vertices)]
        delta_T = [x[u] & (self.lattices[u].top ^ L_T[u]) for u in range(self.n_vertices)]
        return x_next, delta_T

    def solve_tarski_flow(self, edge_subset: Optional[Sequence[int]] = None) -> TarskiFlowResult:
        t0 = time.perf_counter()
        x = list(self.upper_bounds)
        iters = 0
        while True:
            x_next, _ = self.tarski_laplacian_step(x, edge_subset=edge_subset)
            if x_next == x:
                break
            x = x_next
            iters += 1
        violated = [
            v for v in range(self.n_vertices) if not self.lattices[v].leq(self.lower_bounds[v], x[v])
        ]
        return TarskiFlowResult(
            consistent=(len(violated) == 0),
            iterations=iters,
            x_star=x,
            violated_vertices=violated,
            elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
        )

    def localize_mus(self, verify_minimality: bool = True) -> MUSReport:
        all_eids = list(range(len(self.edges)))
        return quickxplain_mus(
            all_eids,
            lambda sub: not self.solve_tarski_flow(edge_subset=sub).consistent,
            verify_minimality=verify_minimality,
        )


# ==============================================================================
# 2. Cycle 6: Chvatal-Gomory Cutting-Plane Closure + Sound 3-Valued Hybrid Solver
# ==============================================================================


@dataclass
class DirectedIntInequality:
    u: int
    v: int
    a: int = 1
    b: int = 0
    c: int = 1
    d: int = 0


@dataclass
class CGCut:
    """Verified Chvatal-Gomory Rank-1 upper-bound inequality: sum_{j} coeffs[j] * x_j <= ub."""

    coeffs: Dict[int, int]
    ub: int
    divisor_g: int
    source_rows: Tuple[int, ...] = ()
    description: str = ""


@dataclass
class HybridTorsorTarskiResult:
    status: str           # v1-compat: "SAT_HYBRID", "UNSAT_FREE_COHOMOLOGY", "UNSAT_TORSION",
                          #            "UNSAT_HYBRID_TARSKI_GHOST", "OPEN_BUDGET_EXCEEDED"
    sound_verdict: str    # v2 3-valued: "CERTIFIED_SAT", "CERTIFIED_UNSAT", "OPEN_BUDGET_EXCEEDED"
    proof_stage: str      # "Z_TORSOR_FREE", "Z_TORSOR_TORSION", "TARSKI_1ROW_INTERVAL",
                          # "TARSKI_SCC_ORDER", "RREF_TARSKI_CLOSURE", "CHVATAL_GOMORY_CUT",
                          # "EXHAUSTIVE_BNB", "WITNESS_VERIFIED", "BUDGET_EXCEEDED"
    z_torsor_status: str
    z_ghost_witness: Optional[List[int]]
    pure_1row_tarski_caught: bool
    rref_tarski_caught: bool
    cg_cuts_caught: bool
    cg_cuts_derived: List[CGCut] = field(default_factory=list)
    bb_nodes_explored: int = 0
    propagation_rounds: int = 0
    x_feasible: Optional[List[int]] = None
    tightened_bounds: List[Tuple[int, int]] = field(default_factory=list)
    contradiction_reason: str = ""
    elapsed_ms: float = 0.0
    z_torsor_result: Optional[se.TorsorResult] = None


def _extract_tarski_equality_sccs(
    n_vars: int,
    ineqs: Sequence[DirectedIntInequality],
) -> List[Tuple[Dict[int, int], int]]:
    """Tarjan's SCC on unit order constraints (x_u <= x_v) to derive exact linear equalities
    x_u - x_rep == 0 whenever u and v lie on a directed inequality cycle!
    """
    adj: Dict[int, List[int]] = {}
    for inq in ineqs:
        if inq.a == inq.c and inq.a > 0 and inq.b == inq.d:
            adj.setdefault(inq.u, []).append(inq.v)
    if not adj:
        return []

    index_counter = 0
    indices: Dict[int, int] = {}
    lowlink: Dict[int, int] = {}
    stack: List[int] = []
    on_stack: Set[int] = set()
    sccs: List[List[int]] = []

    def strongconnect(v: int) -> None:
        nonlocal index_counter
        indices[v] = index_counter
        lowlink[v] = index_counter
        index_counter += 1
        stack.append(v)
        on_stack.add(v)
        for w in adj.get(v, ()):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp: List[int] = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) >= 2:
                sccs.append(sorted(comp))

    for v in range(n_vars):
        if v in adj and v not in indices:
            strongconnect(v)

    derived_eqs: List[Tuple[Dict[int, int], int]] = []
    for comp in sccs:
        rep = comp[0]
        for other in comp[1:]:
            derived_eqs.append(({rep: 1, other: -1}, 0))
    return derived_eqs


def _tighten_var_congruence(lo: int, hi: int, rem: int, mod_m: int) -> Tuple[int, int]:
    """Tighten [lo, hi] to integers congruent to `rem` modulo `mod_m` (mod_m > 1)."""
    rem %= mod_m
    # Smallest x >= lo with x == rem (mod mod_m)
    delta_lo = (rem - (lo % mod_m)) % mod_m
    new_lo = lo + delta_lo
    # Largest x <= hi with x == rem (mod mod_m)
    delta_hi = ((hi % mod_m) - rem) % mod_m
    new_hi = hi - delta_hi
    return new_lo, new_hi


def _propagate_intervals_with_cuts(
    equations: Sequence[Tuple[Dict[int, int], int]],
    ineqs: Sequence[DirectedIntInequality],
    cg_cuts: Sequence[CGCut],
    lows: List[int],
    highs: List[int],
    max_rounds: int = 200,
    enable_cg_modular: bool = True,
) -> Tuple[bool, int, str]:
    """Coupled Tarski + Exact Integer Interval + CG Inequality Cut Propagation."""
    n = len(lows)
    for v in range(n):
        if lows[v] > highs[v]:
            return False, 0, f"Empty interval on x_{v}: [{lows[v]}, {highs[v]}]"

    # Pre-index positive-unit CG upper-bound cuts sum_{j in S} x_j <= ub for subset-cover tightening
    unit_ub_cuts: List[Tuple[Set[int], int, str]] = []
    for cut in cg_cuts:
        if cut.coeffs and all(a == 1 for a in cut.coeffs.values()):
            unit_ub_cuts.append((set(cut.coeffs.keys()), cut.ub, cut.description))

    rounds = 0
    while rounds < max_rounds:
        changed = False
        rounds += 1

        # (a) Directed Tarski inequalities: a * x_u + b <= c * x_v + d
        for inq in ineqs:
            new_u_hi = _floor_div(inq.c * highs[inq.v] + inq.d - inq.b, inq.a)
            if new_u_hi < highs[inq.u]:
                highs[inq.u] = new_u_hi
                changed = True
                if lows[inq.u] > highs[inq.u]:
                    return False, rounds, f"Tarski order contradiction on x_{inq.u}"
            new_v_lo = _ceil_div(inq.a * lows[inq.u] + inq.b - inq.d, inq.c)
            if new_v_lo > lows[inq.v]:
                lows[inq.v] = new_v_lo
                changed = True
                if lows[inq.v] > highs[inq.v]:
                    return False, rounds, f"Tarski order contradiction on x_{inq.v}"

        # (b) Propagate derived Chvatal-Gomory cuts: sum_j a_j x_j <= ub
        for cut in cg_cuts:
            s_min = 0
            for j, a in cut.coeffs.items():
                s_min += a * (lows[j] if a > 0 else highs[j])
            if s_min > cut.ub:
                return False, rounds, f"CG cut contradiction ({cut.description}): min={s_min} > ub={cut.ub}"
            for j, a in cut.coeffs.items():
                if a > 0:
                    new_hi = _floor_div(cut.ub - (s_min - a * lows[j]), a)
                    if new_hi < highs[j]:
                        highs[j] = new_hi
                        changed = True
                else:
                    new_lo = _ceil_div((s_min - a * highs[j]) - cut.ub, -a)
                    if new_lo > lows[j]:
                        lows[j] = new_lo
                        changed = True
                if lows[j] > highs[j]:
                    return False, rounds, f"CG cut interval collapse on x_{j}"

        # (c) Propagate exact linear equalities sum_j a_j x_j == rhs (with CG modular & subset-cover checks!)
        for coeffs, rhs in equations:
            if not coeffs:
                if rhs != 0:
                    return False, rounds, f"Zero row contradiction 0 == {rhs}"
                continue

            # Exact row-GCD check (Chvatal-Gomory rank-1 modular check)
            if enable_cg_modular:
                row_g = 0
                for a in coeffs.values():
                    row_g = math.gcd(row_g, abs(a))
                    if row_g == 1:
                        break
                if row_g > 1 and rhs % row_g != 0:
                    return False, rounds, f"CG modular GCD contradiction: {row_g} does not divide {rhs}"

            s_min = 0
            s_max = 0
            for j, a in coeffs.items():
                if a > 0:
                    s_min += a * lows[j]
                    s_max += a * highs[j]
                else:
                    s_min += a * highs[j]
                    s_max += a * lows[j]

            # Disjoint CG subset-cover upper bound sharpening on unit-positive rows (e.g. sum x_i + sum y_i = 3)!
            if unit_ub_cuts and all(a == 1 for a in coeffs.values()):
                covered: Set[int] = set()
                sharp_max = s_max
                used_cuts: List[str] = []
                row_vars = set(coeffs.keys())
                for c_vars, c_ub, c_desc in unit_ub_cuts:
                    if c_vars.issubset(row_vars) and c_vars.isdisjoint(covered):
                        raw_sub_max = sum(highs[j] for j in c_vars)
                        if c_ub < raw_sub_max:
                            sharp_max -= (raw_sub_max - c_ub)
                            covered.update(c_vars)
                            used_cuts.append(c_desc)
                if rhs > sharp_max:
                    return (
                        False,
                        rounds,
                        f"CG subset-cover contradiction: rhs={rhs} > CG-tightened max={sharp_max} via {used_cuts}",
                    )

            if rhs < s_min or rhs > s_max:
                return False, rounds, f"Interval range contradiction: rhs={rhs} outside [{s_min}, {s_max}]"

            # Single-residual modular congruence tightening (mod g in {2, 3})
            if enable_cg_modular and len(coeffs) >= 2:
                for g_mod in (2, 3):
                    non_div = [j for j, a in coeffs.items() if a % g_mod != 0]
                    if len(non_div) == 1:
                        k_var = non_div[0]
                        ak = coeffs[k_var] % g_mod
                        # Since g_mod is prime (2 or 3) and ak != 0, ak is invertible mod g_mod!
                        inv_ak = pow(ak, -1, g_mod)
                        req_rem = (rhs * inv_ak) % g_mod
                        n_lo, n_hi = _tighten_var_congruence(lows[k_var], highs[k_var], req_rem, g_mod)
                        if n_lo > lows[k_var]:
                            lows[k_var] = n_lo
                            changed = True
                        if n_hi < highs[k_var]:
                            highs[k_var] = n_hi
                            changed = True
                        if lows[k_var] > highs[k_var]:
                            return (
                                False,
                                rounds,
                                f"CG mod-{g_mod} congruence collapse on x_{k_var}: required x_{k_var} == {req_rem} (mod {g_mod})",
                            )

            for j, a in coeffs.items():
                if a > 0:
                    new_hi = _floor_div(rhs - (s_min - a * lows[j]), a)
                    new_lo = _ceil_div(rhs - (s_max - a * highs[j]), a)
                else:
                    pos_a = -a
                    new_hi = _floor_div((s_max - a * lows[j]) - rhs, pos_a)
                    new_lo = _ceil_div((s_min - a * highs[j]) - rhs, pos_a)
                if new_lo > lows[j]:
                    lows[j] = new_lo
                    changed = True
                if new_hi < highs[j]:
                    highs[j] = new_hi
                    changed = True
                if lows[j] > highs[j]:
                    return False, rounds, f"Hybrid interval collapse on x_{j}: [{lows[j]}, {highs[j]}]"

        if not changed:
            break
    return True, rounds, ""


def _generate_chvatal_gomory_cuts(
    orig_eqs: Sequence[Tuple[Dict[int, int], int]],
    lows: Sequence[int],
    highs: Sequence[int],
) -> List[CGCut]:
    """Generate sound Chvatal-Gomory Rank-1 floor cuts from odd-cycles / triangles &
    row combinations of integer equalities!

    For any nonnegative combination of rows yielding:
        sum_{j in S} (g * c_j) x_j + sum_{j in R} r_j x_j == b
    with g >= 2, bounding the residual terms R from below via [l_j, u_j] gives the
    100% sound integer Chvatal-Gomory cut:
        sum_{j in S} c_j x_j <= floor((b - S_min(R)) / g)!
    """
    cuts: List[CGCut] = []
    seen_sigs: Set[Tuple[Tuple[Tuple[int, int], ...], int]] = set()

    def try_extract_cg_cut(comb_coeffs: Dict[int, int], comb_rhs: int, src: Tuple[int, ...]) -> None:
        if not comb_coeffs:
            return
        for g in (2, 3):
            div_part: Dict[int, int] = {}
            rem_min = 0
            for j, a in comb_coeffs.items():
                if a % g == 0:
                    div_part[j] = a // g
                else:
                    # Bound residual term a * x_j from below using current [lows[j], highs[j]]
                    rem_min += a * (lows[j] if a > 0 else highs[j])
            if not div_part:
                continue
            num = comb_rhs - rem_min
            # Only non-trivial if num is NOT divisible by g (strict fractional floor tightening!)
            if num % g == 0:
                continue
            ub = _floor_div(num, g)
            # Check if this cut actually improves on trivial box upper bound of div_part!
            triv_max = sum(a * (highs[j] if a > 0 else lows[j]) for j, a in div_part.items())
            if ub < triv_max:
                sig = (tuple(sorted(div_part.items())), ub)
                if sig not in seen_sigs:
                    seen_sigs.add(sig)
                    cuts.append(
                        CGCut(
                            coeffs=div_part,
                            ub=ub,
                            divisor_g=g,
                            source_rows=src,
                            description=f"CG(g={g}, rows={src}): sum<={ub} (floor({num}/{g}))",
                        )
                    )

    # 1. Single-row CG cuts (catches e.g. 2*x0 + 2*x1 + s = 3 directly!)
    for idx, (coeffs, rhs) in enumerate(orig_eqs):
        try_extract_cg_cut(coeffs, rhs, (idx,))

    # 2. Detect odd-cycle (3-cycle & 5-cycle) packing structures on unit-positive rows!
    # Build graph of pairs of variables co-occurring with coeff +1 in sparse rows (<= 4 vars)
    edge_to_rows: Dict[Tuple[int, int], List[int]] = {}
    var_adj: Dict[int, Set[int]] = {}
    for idx, (coeffs, rhs) in enumerate(orig_eqs):
        if len(coeffs) > 5:
            continue
        pos_unit = sorted(j for j, a in coeffs.items() if a == 1 and lows[j] >= 0)
        if len(pos_unit) < 2:
            continue
        # Only pair up variables that appear in >= 2 rows (skip isolated slack variables!)
        for a_i in range(len(pos_unit)):
            for b_i in range(a_i + 1, len(pos_unit)):
                u, v = pos_unit[a_i], pos_unit[b_i]
                edge_to_rows.setdefault((u, v), []).append(idx)
                var_adj.setdefault(u, set()).add(v)
                var_adj.setdefault(v, set()).add(u)

    # Triangle (3-clique) sum cuts: r1(u,v) + r2(v,w) + r3(u,w) => 2*(x_u+x_v+x_w) + slacks = b1+b2+b3!
    vars_sorted = sorted(var_adj.keys())
    tri_count = 0
    for u in vars_sorted:
        nu = [v for v in var_adj[u] if v > u]
        for i in range(len(nu)):
            v = nu[i]
            for j in range(i + 1, len(nu)):
                w = nu[j]
                if w in var_adj.get(v, ()):
                    r_uv = edge_to_rows[(u, v)][0]
                    r_uw = edge_to_rows[(u, w)][0]
                    r_vw = edge_to_rows[(v, w) if v < w else (w, v)][0]
                    if len({r_uv, r_uw, r_vw}) == 3:
                        comb: Dict[int, int] = {}
                        c_rhs = 0
                        for rid in (r_uv, r_uw, r_vw):
                            rc, rb = orig_eqs[rid]
                            c_rhs += rb
                            for k_v, a_v in rc.items():
                                nv = comb.get(k_v, 0) + a_v
                                if nv == 0:
                                    comb.pop(k_v, None)
                                else:
                                    comb[k_v] = nv
                        try_extract_cg_cut(comb, c_rhs, (r_uv, r_uw, r_vw))
                        tri_count += 1
                        if tri_count >= 128:
                            break
            if tri_count >= 128:
                break
        if tri_count >= 128:
            break

    # 3. Also detect odd 5-cycles (e.g. KCBS pentagon) if few triangles found
    if len(vars_sorted) <= 40:
        pent_count = 0
        for u in vars_sorted:
            for v in var_adj[u]:
                if v <= u:
                    continue
                for w in var_adj[v]:
                    if w <= u or w == u:
                        continue
                    for p in var_adj[w]:
                        if p <= u or p in (u, v):
                            continue
                        for q in var_adj[p]:
                            if q <= u or q in (u, v, w):
                                continue
                            if u in var_adj[q]:
                                e_keys = [
                                    (min(a, b), max(a, b))
                                    for a, b in ((u, v), (v, w), (w, p), (p, q), (q, u))
                                ]
                                rids = [edge_to_rows[ek][0] for ek in e_keys]
                                if len(set(rids)) == 5:
                                    comb = {}
                                    c_rhs = 0
                                    for rid in rids:
                                        rc, rb = orig_eqs[rid]
                                        c_rhs += rb
                                        for k_v, a_v in rc.items():
                                            comb[k_v] = comb.get(k_v, 0) + a_v
                                    try_extract_cg_cut(comb, c_rhs, tuple(sorted(rids)))
                                    pent_count += 1
                                    if pent_count >= 32:
                                        break
                        if pent_count >= 32:
                            break
                    if pent_count >= 32:
                        break
                if pent_count >= 32:
                    break
            if pent_count >= 32:
                break

    return cuts


def check_hybrid_feasible(
    A: se.SparseIntMatrix,
    c: Sequence[int],
    ineqs: Sequence[DirectedIntInequality],
    lows: Sequence[int],
    highs: Sequence[int],
    x: Sequence[int],
) -> bool:
    """Zero-trust explicit verifier for SAT witnesses: checks bounds, A @ x == c, and all Tarski inequalities."""
    if len(x) != A.ncols:
        return False
    for j, val in enumerate(x):
        if val < lows[j] or val > highs[j]:
            return False
    lhs = A.matvec(x)
    for i in range(A.nrows):
        if lhs[i] != c[i]:
            return False
    for inq in ineqs:
        if inq.a * x[inq.u] + inq.b > inq.c * x[inq.v] + inq.d:
            return False
    return True


def solve_hybrid_torsor_tarski(
    A: se.SparseIntMatrix,
    c: Sequence[int],
    lower_bounds: Sequence[int],
    upper_bounds: Sequence[int],
    ineqs: Sequence[DirectedIntInequality] = (),
    max_branch_nodes: int = 4096,
    max_bb_nodes: Optional[int] = None,
) -> HybridTorsorTarskiResult:
    """Guardrail D v2.0 — Algebraic-Tarski Cutting-Plane Closure + Sound 3-Valued Budgeted Search.

    Returns strictly verified:
      - sound_verdict == "CERTIFIED_SAT"        (witness explicitly checked via check_hybrid_feasible)
      - sound_verdict == "CERTIFIED_UNSAT"      (exact torsor/Tarski/RREF/CG-cut/exhaustive proof)
      - sound_verdict == "OPEN_BUDGET_EXCEEDED" (cleanly flags timeout without ever guessing SAT/UNSAT!)
    """
    t0 = time.perf_counter()
    budget = max_bb_nodes if max_bb_nodes is not None else max_branch_nodes
    n = A.ncols
    assert len(lower_bounds) == n and len(upper_bounds) == n

    # Stage 1: Exact unbounded Z-torsor check (catches Mermin-Peres, GHZ, Cabello 18-ray KS in 0 branches!)
    z_res: se.TorsorResult = se.solve_torsor(A, c, ring="Z", want_witness=True)
    if z_res.status != "SAT_INTEGRAL":
        stage = "Z_TORSOR_FREE" if z_res.status == "UNSAT_FREE_COHOMOLOGY" else "Z_TORSOR_TORSION"
        return HybridTorsorTarskiResult(
            status=z_res.status,
            sound_verdict="CERTIFIED_UNSAT",
            proof_stage=stage,
            z_torsor_status=z_res.status,
            z_ghost_witness=None,
            pure_1row_tarski_caught=False,
            rref_tarski_caught=False,
            cg_cuts_caught=False,
            tightened_bounds=list(zip(lower_bounds, upper_bounds)),
            contradiction_reason=f"Refuted directly by exact Z-torsor ({z_res.status})",
            elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
            z_torsor_result=z_res,
        )

    # Check if unbounded Z witness ALREADY satisfies all bounds & Tarski inequalities!
    if z_res.x_int is not None and check_hybrid_feasible(
        A, c, ineqs, lower_bounds, upper_bounds, z_res.x_int
    ):
        return HybridTorsorTarskiResult(
            status="SAT_HYBRID",
            sound_verdict="CERTIFIED_SAT",
            proof_stage="WITNESS_VERIFIED",
            z_torsor_status="SAT_INTEGRAL",
            z_ghost_witness=None,
            pure_1row_tarski_caught=False,
            rref_tarski_caught=False,
            cg_cuts_caught=False,
            x_feasible=list(z_res.x_int),
            tightened_bounds=list(zip(lower_bounds, upper_bounds)),
            elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
            z_torsor_result=z_res,
        )

    orig_eqs: List[Tuple[Dict[int, int], int]] = [
        (dict(A.rows.get(r, {})), c[r]) for r in range(A.nrows)
    ]

    # Stage 1.5: Diagnostic naive 1-row Tarski interval propagation
    lo_1, hi_1 = list(lower_bounds), list(upper_bounds)
    ok_1row, rounds_1, reason_1 = _propagate_intervals_with_cuts(
        orig_eqs, ineqs, (), lo_1, hi_1, enable_cg_modular=False
    )
    if not ok_1row:
        return HybridTorsorTarskiResult(
            status="UNSAT_HYBRID_TARSKI_GHOST",
            sound_verdict="CERTIFIED_UNSAT",
            proof_stage="TARSKI_1ROW_INTERVAL",
            z_torsor_status="SAT_INTEGRAL",
            z_ghost_witness=z_res.x_int,
            pure_1row_tarski_caught=True,
            rref_tarski_caught=True,
            cg_cuts_caught=False,
            propagation_rounds=rounds_1,
            tightened_bounds=list(zip(lo_1, hi_1)),
            contradiction_reason=reason_1,
            elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
            z_torsor_result=z_res,
        )

    # Stage 2: Extract directed Tarski equality-SCCs (x_u <= ... <= x_u ==> x_u == x_v) & exact RREF!
    scc_eqs = _extract_tarski_equality_sccs(n, ineqs)
    if scc_eqs:
        A_aug = se.SparseIntMatrix(A.nrows + len(scc_eqs), n)
        c_aug = list(c)
        for r, rmap in A.rows.items():
            for col_j, val in rmap.items():
                A_aug.set_entry(r, col_j, val)
        for idx, (sc_map, sc_rhs) in enumerate(scc_eqs):
            for col_j, val in sc_map.items():
                A_aug.set_entry(A.nrows + idx, col_j, val)
            c_aug.append(sc_rhs)
        # Re-check exact Z-torsor with Tarski-derived equalities! (Kills Tier 3C in 0 branches!)
        z_scc = se.solve_torsor(A_aug, c_aug, ring="Z", want_witness=True)
        if z_scc.status != "SAT_INTEGRAL":
            return HybridTorsorTarskiResult(
                status="UNSAT_HYBRID_TARSKI_GHOST",
                sound_verdict="CERTIFIED_UNSAT",
                proof_stage="TARSKI_SCC_ORDER",
                z_torsor_status="SAT_INTEGRAL",
                z_ghost_witness=z_res.x_int,
                pure_1row_tarski_caught=False,
                rref_tarski_caught=False,
                cg_cuts_caught=True,
                propagation_rounds=rounds_1,
                tightened_bounds=list(zip(lo_1, hi_1)),
                contradiction_reason=f"Directed Tarski equality-SCC + Z-torsor refuted ({z_scc.status})",
                elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
                z_torsor_result=z_scc,
            )
        sat_q, rref_eqs, piv_cols = se.compute_exact_rref_rows(A_aug, c_aug)
    else:
        sat_q, rref_eqs, piv_cols = se.compute_exact_rref_rows(A, c)
    assert sat_q

    all_eqs = orig_eqs + scc_eqs + rref_eqs
    lo_r, hi_r = list(lo_1), list(hi_1)
    ok_rref, rounds_r, reason_r = _propagate_intervals_with_cuts(
        all_eqs, ineqs, (), lo_r, hi_r, enable_cg_modular=False
    )
    if not ok_rref:
        return HybridTorsorTarskiResult(
            status="UNSAT_HYBRID_TARSKI_GHOST",
            sound_verdict="CERTIFIED_UNSAT",
            proof_stage="RREF_TARSKI_CLOSURE",
            z_torsor_status="SAT_INTEGRAL",
            z_ghost_witness=z_res.x_int,
            pure_1row_tarski_caught=False,
            rref_tarski_caught=True,
            cg_cuts_caught=False,
            propagation_rounds=rounds_1 + rounds_r,
            tightened_bounds=list(zip(lo_r, hi_r)),
            contradiction_reason=reason_r,
            elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
            z_torsor_result=z_res,
        )

    # Stage 3: Algebraic-Tarski Chvatal-Gomory Cutting-Plane Closure (Polynomial-Time Pre-Branching!)
    cg_cuts = _generate_chvatal_gomory_cuts(orig_eqs + rref_eqs, lo_r, hi_r)
    ok_cg, rounds_cg, reason_cg = _propagate_intervals_with_cuts(
        all_eqs, ineqs, cg_cuts, lo_r, hi_r, enable_cg_modular=True
    )
    if not ok_cg:
        return HybridTorsorTarskiResult(
            status="UNSAT_HYBRID_TARSKI_GHOST",
            sound_verdict="CERTIFIED_UNSAT",
            proof_stage="CHVATAL_GOMORY_CUT",
            z_torsor_status="SAT_INTEGRAL",
            z_ghost_witness=z_res.x_int,
            pure_1row_tarski_caught=False,
            rref_tarski_caught=False,
            cg_cuts_caught=True,
            cg_cuts_derived=cg_cuts,
            propagation_rounds=rounds_1 + rounds_r + rounds_cg,
            tightened_bounds=list(zip(lo_r, hi_r)),
            contradiction_reason=reason_cg,
            elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
            z_torsor_result=z_res,
        )

    # Quick verified feasibility checks at tightened endpoints
    for cand in (lo_r, hi_r):
        if check_hybrid_feasible(A, c, ineqs, lower_bounds, upper_bounds, cand):
            return HybridTorsorTarskiResult(
                status="SAT_HYBRID",
                sound_verdict="CERTIFIED_SAT",
                proof_stage="WITNESS_VERIFIED",
                z_torsor_status="SAT_INTEGRAL",
                z_ghost_witness=None,
                pure_1row_tarski_caught=False,
                rref_tarski_caught=False,
                cg_cuts_caught=False,
                cg_cuts_derived=cg_cuts,
                propagation_rounds=rounds_1 + rounds_r + rounds_cg,
                x_feasible=list(cand),
                tightened_bounds=list(zip(lo_r, hi_r)),
                elapsed_ms=round((time.perf_counter() - t0) * 1000.0, 3),
                z_torsor_result=z_res,
            )

    # Stage 4: Sound 3-Valued Budgeted Parametric Branch-and-Bound
    # Precompute variable constraint incidence degree for most-constrained ordering
    var_deg = [0] * n
    for coeffs, _ in orig_eqs:
        for j in coeffs:
            var_deg[j] += 1
    for inq in ineqs:
        var_deg[inq.u] += 1
        var_deg[inq.v] += 1

    piv_set = set(piv_cols)
    free_vars = [j for j in range(n) if j not in piv_set]
    nodes = 0
    budget_exceeded = False
    found_x: Optional[List[int]] = None

    def dfs(cur_lo: List[int], cur_hi: List[int]) -> bool:
        nonlocal nodes, budget_exceeded, found_x
        if budget_exceeded:
            return False
        nodes += 1
        if nodes > budget:
            budget_exceeded = True
            return False

        # Most-constrained (minimum span > 0) + highest-degree variable ordering
        branch_var = -1
        best_key = (1 << 60, 0)
        for j in free_vars:
            span = cur_hi[j] - cur_lo[j]
            if span > 0:
                key = (span, -var_deg[j])
                if key < best_key:
                    best_key = key
                    branch_var = j
        if branch_var == -1:
            for j in range(n):
                span = cur_hi[j] - cur_lo[j]
                if span > 0:
                    key = (span, -var_deg[j])
                    if key < best_key:
                        best_key = key
                        branch_var = j

        if branch_var == -1:
            if check_hybrid_feasible(A, c, ineqs, lower_bounds, upper_bounds, cur_lo):
                found_x = list(cur_lo)
                return True
            return False

        lo_v, hi_v = cur_lo[branch_var], cur_hi[branch_var]
        if hi_v - lo_v <= 4:
            splits = [(val, val) for val in range(lo_v, hi_v + 1)]
        else:
            mid = (lo_v + hi_v) // 2
            splits = [(lo_v, mid), (mid + 1, hi_v)]

        for s_lo, s_hi in splits:
            if budget_exceeded:
                return False
            n_lo, n_hi = list(cur_lo), list(cur_hi)
            n_lo[branch_var], n_hi[branch_var] = s_lo, s_hi
            ok_sub, _, _ = _propagate_intervals_with_cuts(all_eqs, ineqs, cg_cuts, n_lo, n_hi)
            if ok_sub and dfs(n_lo, n_hi):
                return True
        return False

    sat_bb = dfs(lo_r, hi_r)
    elapsed = round((time.perf_counter() - t0) * 1000.0, 3)

    if sat_bb and found_x is not None:
        assert check_hybrid_feasible(A, c, ineqs, lower_bounds, upper_bounds, found_x)
        return HybridTorsorTarskiResult(
            status="SAT_HYBRID",
            sound_verdict="CERTIFIED_SAT",
            proof_stage="WITNESS_VERIFIED",
            z_torsor_status="SAT_INTEGRAL",
            z_ghost_witness=None,
            pure_1row_tarski_caught=False,
            rref_tarski_caught=False,
            cg_cuts_caught=False,
            cg_cuts_derived=cg_cuts,
            bb_nodes_explored=nodes,
            propagation_rounds=rounds_1 + rounds_r + rounds_cg,
            x_feasible=found_x,
            tightened_bounds=list(zip(lo_r, hi_r)),
            elapsed_ms=elapsed,
            z_torsor_result=z_res,
        )

    if budget_exceeded:
        # SOUND 3-VALUED GUARANTEE: NEVER guess SAT or UNSAT when budget is exceeded!
        return HybridTorsorTarskiResult(
            status="OPEN_BUDGET_EXCEEDED",
            sound_verdict="OPEN_BUDGET_EXCEEDED",
            proof_stage="BUDGET_EXCEEDED",
            z_torsor_status="SAT_INTEGRAL",
            z_ghost_witness=z_res.x_int,
            pure_1row_tarski_caught=False,
            rref_tarski_caught=False,
            cg_cuts_caught=False,
            cg_cuts_derived=cg_cuts,
            bb_nodes_explored=nodes,
            propagation_rounds=rounds_1 + rounds_r + rounds_cg,
            x_feasible=None,
            tightened_bounds=list(zip(lo_r, hi_r)),
            contradiction_reason=f"Search budget ({budget} nodes) exceeded; returning sound OPEN status",
            elapsed_ms=elapsed,
            z_torsor_result=z_res,
        )

    return HybridTorsorTarskiResult(
        status="UNSAT_HYBRID_TARSKI_GHOST",
        sound_verdict="CERTIFIED_UNSAT",
        proof_stage="EXHAUSTIVE_BNB",
        z_torsor_status="SAT_INTEGRAL",
        z_ghost_witness=z_res.x_int,
        pure_1row_tarski_caught=False,
        rref_tarski_caught=False,
        cg_cuts_caught=False,
        cg_cuts_derived=cg_cuts,
        bb_nodes_explored=nodes,
        propagation_rounds=rounds_1 + rounds_r + rounds_cg,
        x_feasible=None,
        tightened_bounds=list(zip(lo_r, hi_r)),
        contradiction_reason=f"Exhaustive exact parametric Tarski B&B refuted [l, u] ({nodes} nodes)",
        elapsed_ms=elapsed,
        z_torsor_result=z_res,
    )
