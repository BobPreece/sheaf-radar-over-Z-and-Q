"""Adversarial Paradox & Decoy Generators (Red-Team Sophist Suite).

Covers all 5 Paradox Classes + Consistent Controls:
  1. Purity-Gate Scale-Trap Cycles ({-2,-1,0,1,2}) & Non-Dyadic Hilbert/Cauchy Decoys
  2. Penrose Affine Staircases & Z_m Mobius / Liar Torsion Loops
  3. Hollow Simplicial Spheres (dDelta^3, S^2) & 6-Vertex RP^2 Hemi-Icosahedron
  4. Camouflaged Shared-Edge Decoy Mazes (T = 12..500 consistent triangles)
  5. Asymmetric Horn DAGs, Powerset Galois Sheaves & Giovanni Caru Ghost Paradoxes.

Strictly Python 3 stdlib only. Zero fractions.Fraction usage.
"""

import math
import random
from typing import List, Tuple

from .cellular_complex import CellularSheaf1Complex, Rat, Simplicial2Complex
from .sparse_exact import SparseIntMatrix
from .tarski_hybrid import (
    BitmaskPowersetLattice,
    DirectedIntInequality,
    GaloisConnection,
    TarskiLatticeSheaf,
)


def _rat_norm(num: int, den: int) -> Rat:
    if den < 0:
        num, den = -num, -den
    if num == 0:
        return (0, 1)
    g = math.gcd(abs(num), den)
    return (num // g, den // g)


def _rat_add(a: Rat, b: Rat) -> Rat:
    return _rat_norm(a[0] * b[1] + b[0] * a[1], a[1] * b[1])


def _rat_sub(a: Rat, b: Rat) -> Rat:
    return _rat_norm(a[0] * b[1] - b[0] * a[1], a[1] * b[1])


def _rat_mul(a: Rat, b: Rat) -> Rat:
    return _rat_norm(a[0] * b[0], a[1] * b[1])


def exact_hilbert_matrix(d: int) -> List[List[Rat]]:
    return [[(1, i + j + 1) for j in range(d)] for i in range(d)]


def exact_hilbert_inverse(d: int) -> List[List[Rat]]:
    inv: List[List[Rat]] = []
    for i in range(d):
        row: List[Rat] = []
        for j in range(d):
            sign = -1 if ((i + j) & 1) else 1
            val = (
                sign
                * (i + j + 1)
                * math.comb(d + i, d - j - 1)
                * math.comb(d + j, d - i - 1)
                * (math.comb(i + j, i) ** 2)
            )
            row.append((val, 1))
        inv.append(row)
    return inv


def exact_cauchy_matrix(d: int) -> List[List[Rat]]:
    return [[(1, 2 * i + 2 * j + 3) for j in range(d)] for i in range(d)]


def exact_cauchy_inverse(d: int) -> List[List[Rat]]:
    a = [2 * i + 1 for i in range(d)]
    b = [2 * j + 2 for j in range(d)]
    inv: List[List[Rat]] = []
    for i in range(d):
        row: List[Rat] = []
        for j in range(d):
            num = 1
            for k in range(d):
                num *= (a[j] + b[k]) * (a[k] + b[i])
            den = a[j] + b[i]
            for k in range(d):
                if k != j:
                    den *= (a[j] - a[k])
                if k != i:
                    den *= (b[i] - b[k])
            row.append(_rat_norm(num, den))
        inv.append(row)
    return inv


def _identity_rat(d: int) -> List[List[Rat]]:
    return [[(1, 1) if i == j else (0, 1) for j in range(d)] for i in range(d)]


def _matvec_rat(M: List[List[Rat]], x: List[Rat]) -> List[Rat]:
    out: List[Rat] = []
    for row in M:
        acc: Rat = (0, 1)
        for m_ij, x_j in zip(row, x):
            if m_ij[0] != 0 and x_j[0] != 0:
                acc = _rat_add(acc, _rat_mul(m_ij, x_j))
        out.append(acc)
    return out


# ---- Class 1: Float64 Cliff & Non-Dyadic False-Positive Decoys ----


def build_purity_gate_scale_trap_homogeneous(N: int) -> CellularSheaf1Complex:
    if N < 6 or N % 2 != 0:
        raise ValueError("N must be an even integer >= 6")
    K = N // 2
    sh = CellularSheaf1Complex(ring="Z")
    sh.add_vertices(N, stalk_dim=1)
    for i in range(K):
        sh.add_scalar_edge(i, i + 1, coeff_u=2, coeff_v=1, rhs=0, label=f"up_{i}")
    for i in range(K, N - 1):
        sh.add_scalar_edge(i, i + 1, coeff_u=1, coeff_v=2, rhs=0, label=f"dn_{i}")
    sh.add_scalar_edge(0, N - 1, coeff_u=1, coeff_v=1, rhs=0, label="close_mismatch")
    return sh


def build_purity_gate_scale_trap_torsor(N: int) -> CellularSheaf1Complex:
    if N < 6 or N % 2 != 0:
        raise ValueError("N must be an even integer >= 6")
    K = N // 2
    sh = CellularSheaf1Complex(ring="Z")
    sh.add_vertices(N, stalk_dim=1)
    for i in range(K):
        sh.add_scalar_edge(i, i + 1, coeff_u=2, coeff_v=1, rhs=0, label=f"up_{i}")
    for i in range(K, N - 1):
        sh.add_scalar_edge(i, i + 1, coeff_u=1, coeff_v=2, rhs=(1 if i == K else 0), label=f"dn_{i}")
    sh.add_scalar_edge(0, N - 1, coeff_u=2, coeff_v=1, rhs=0, label="close_consistent")
    return sh


def build_consistent_nondyadic_loop(
    d: int, family: str = "hilbert", mode: str = "inverse_holonomy"
) -> Tuple[CellularSheaf1Complex, List[List[Rat]]]:
    if family == "hilbert":
        M, M_inv = exact_hilbert_matrix(d), exact_hilbert_inverse(d)
    elif family == "cauchy":
        M, M_inv = exact_cauchy_matrix(d), exact_cauchy_inverse(d)
    else:
        raise ValueError(f"Unknown family {family!r}")
    I_d = _identity_rat(d)
    sh = CellularSheaf1Complex(ring="Q")

    if mode == "symmetric_bounded":
        sh.add_vertices(3, stalk_dim=d)
        x0 = [(i + 1, 1) for i in range(d)]
        x1 = [(2 * i + 1, 1) for i in range(d)]
        x2 = [(i + 3, 1) for i in range(d)]
        mx0, mx1, mx2 = _matvec_rat(M, x0), _matvec_rat(M, x1), _matvec_rat(M, x2)
        c0 = [_rat_sub(mx1[i], mx0[i]) for i in range(d)]
        c1 = [_rat_sub(mx2[i], mx1[i]) for i in range(d)]
        c2 = [_rat_sub(mx0[i], mx2[i]) for i in range(d)]
        sh.add_edge(0, 1, F_u=M, F_v=M, c_e=c0, label=f"{family}_e0")
        sh.add_edge(1, 2, F_u=M, F_v=M, c_e=c1, label=f"{family}_e1")
        sh.add_edge(2, 0, F_u=M, F_v=M, c_e=c2, label=f"{family}_e2")
        return sh, [x0, x1, x2]

    if mode == "inverse_holonomy":
        sh.add_vertices(2, stalk_dim=d)
        x0 = [(i + 1, 1) for i in range(d)]
        mx0 = _matvec_rat(M, x0)
        x1 = [_rat_add(mx0[i], (1, 1)) for i in range(d)]
        c0 = [_rat_sub(x1[i], mx0[i]) for i in range(d)]
        minv_x1 = _matvec_rat(M_inv, x1)
        c1 = [_rat_sub(x0[i], minv_x1[i]) for i in range(d)]
        sh.add_edge(0, 1, F_u=M, F_v=I_d, c_e=c0, label=f"{family}_fwd")
        sh.add_edge(1, 0, F_u=M_inv, F_v=I_d, c_e=c1, label=f"{family}_inv")
        sh.pin_anchor(0, x0)
        return sh, [x0, x1]

    raise ValueError(f"Unknown mode {mode!r}")


# ---- Class 2: Penrose Staircases & Z_m Torsion Loops ----


def build_penrose_staircase(N: int, step: int = 1) -> CellularSheaf1Complex:
    sh = CellularSheaf1Complex(ring="Z")
    sh.add_vertices(N, stalk_dim=1)
    for i in range(N):
        sh.add_scalar_edge(i, (i + 1) % N, coeff_u=1, coeff_v=1, rhs=step, label=f"step_{i}")
    return sh


def build_zm_torsion_loop(N: int, m: int, defect: int = 1) -> CellularSheaf1Complex:
    if N < 3 or m < 2:
        raise ValueError("Require N >= 3 and m >= 2")
    sh = CellularSheaf1Complex(ring="Z")
    sh.add_vertices(N, stalk_dim=1)
    for i in range(N - 1):
        sh.add_scalar_edge(i, i + 1, coeff_u=1, coeff_v=1, rhs=0, label=f"chain_{i}")
    sh.add_scalar_edge(0, N - 1, coeff_u=-(m - 1), coeff_v=1, rhs=defect, label=f"twist_Z{m}")
    return sh


def build_consistent_tree_with_anchor(N: int, seed: int = 1) -> CellularSheaf1Complex:
    sh = CellularSheaf1Complex(ring="Z")
    sh.add_vertices(N, stalk_dim=1)
    x_true = [((i * 7 + seed * 13) % 11) - 5 for i in range(N)]
    for i in range(1, N):
        parent = (i - 1) // 2
        sh.add_scalar_edge(parent, i, coeff_u=1, coeff_v=1, rhs=x_true[i] - x_true[parent])
    sh.pin_anchor(0, [x_true[0]])
    return sh


# ---- Class 3: Simplicial H^2 Spheres & 6-Vertex RP^2 Hemi-Icosahedron ----


def build_hollow_tetrahedron_dDelta3(defect: int = 1) -> Simplicial2Complex:
    cx = Simplicial2Complex(n_vertices=4)
    for idx, (u, v, w) in enumerate([(1, 2, 3), (0, 3, 2), (0, 1, 3), (0, 2, 1)]):
        cx.add_triangle(u, v, w, rhs=(defect if idx == 0 else 0), label=f"tet_F{idx}")
    assert cx.verify_functoriality()
    return cx


def build_hollow_octahedron_S2(defect: int = 1) -> Simplicial2Complex:
    cx = Simplicial2Complex(n_vertices=6)
    faces = [(0, 2, 4), (2, 1, 4), (1, 3, 4), (3, 0, 4), (2, 0, 5), (1, 2, 5), (3, 1, 5), (0, 3, 5)]
    for idx, (u, v, w) in enumerate(faces):
        cx.add_triangle(u, v, w, rhs=(defect if idx == 0 else 0), label=f"oct_F{idx}")
    assert cx.verify_functoriality()
    return cx


def build_subdivided_sphere_S2(defect: int = 1) -> Simplicial2Complex:
    cx = Simplicial2Complex(n_vertices=12)
    faces: List[Tuple[int, int, int]] = []
    for i in range(5):
        u, v = 1 + i, 1 + ((i + 1) % 5)
        faces.append((0, u, v))
    for i in range(5):
        u, v = 1 + i, 1 + ((i + 1) % 5)
        lw, lw_next = 6 + i, 6 + ((i + 1) % 5)
        faces.append((u, lw, v))
        faces.append((v, lw, lw_next))
    for i in range(5):
        lw, lw_next = 6 + i, 6 + ((i + 1) % 5)
        faces.append((11, lw_next, lw))
    for idx, (u, v, w) in enumerate(faces):
        cx.add_triangle(u, v, w, rhs=(defect if idx == 0 else 0), label=f"ico_F{idx}")
    assert cx.verify_functoriality()
    return cx


def build_rp2_hemi_icosahedron(defect: int = 1) -> Simplicial2Complex:
    cx = Simplicial2Complex(n_vertices=6)
    triangles = [
        (0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 5, 1),
        (1, 2, 4), (2, 3, 5), (3, 4, 1), (4, 5, 2), (5, 1, 3),
    ]
    for idx, (u, v, w) in enumerate(triangles):
        cx.add_triangle(u, v, w, rhs=(defect if idx == 0 else 0), label=f"RP2_T{idx}")
    assert cx.verify_functoriality()
    return cx


# ---- Class 4: Camouflaged Shared-Edge Decoy Mazes ----


def build_shared_edge_decoy_maze(
    loop_len: int = 6, n_decoy_triangles: int = 100, seed: int = 20261119
) -> Tuple[CellularSheaf1Complex, List[int], int]:
    if loop_len < 4:
        raise ValueError("loop_len must be >= 4")
    rng = random.Random(seed)
    sh = CellularSheaf1Complex(ring="Z")
    sh.add_vertices(loop_len, stalk_dim=1)

    culprit_edges: List[int] = []
    consistent_edges: List[Tuple[int, int]] = []
    for i in range(loop_len - 1):
        eid = sh.add_scalar_edge(i, i + 1, coeff_u=1, coeff_v=1, rhs=0, label=f"Cbad_{i}")
        culprit_edges.append(eid)
        consistent_edges.append((i, i + 1))

    fault_eid = sh.add_scalar_edge(loop_len - 1, 0, coeff_u=1, coeff_v=1, rhs=1, label="Cbad_FAULT")
    culprit_edges.append(fault_eid)

    heavy_targets = consistent_edges[: max(1, loop_len - 3)]
    light_targets = consistent_edges[max(1, loop_len - 3) :]
    mesh_pool: List[Tuple[int, int]] = list(heavy_targets)

    for t in range(n_decoy_triangles):
        if t < len(light_targets):
            a, b = light_targets[t]
            w = sh.add_vertex(stalk_dim=1)
            sh.add_scalar_edge(a, w, 1, 1, 0, label=f"decoy_light_T{t}_a")
            sh.add_scalar_edge(w, b, 1, 1, 0, label=f"decoy_light_T{t}_b")
        else:
            a, b = heavy_targets[t % len(heavy_targets)] if (t % 2 == 0) else mesh_pool[rng.randrange(len(mesh_pool))]
            w = sh.add_vertex(stalk_dim=1)
            sh.add_scalar_edge(a, w, 1, 1, 0, label=f"decoy_heavy_T{t}_a")
            sh.add_scalar_edge(w, b, 1, 1, 0, label=f"decoy_heavy_T{t}_b")
            mesh_pool.append((a, w))
            mesh_pool.append((w, b))

    return sh, culprit_edges, fault_eid


# ---- Class 5: Asymmetric Horn DAGs, Powerset Galois & Caru Ghost Paradoxes ----


def build_valid_asymmetric_horn_dag(depth: int = 12) -> Tuple[TarskiLatticeSheaf, CellularSheaf1Complex]:
    bool_lat = BitmaskPowersetLattice(1)
    n_verts = depth + 3
    tsh = TarskiLatticeSheaf([bool_lat] * n_verts)
    lsh = CellularSheaf1Complex(ring="Z")
    lsh.add_vertices(n_verts, stalk_dim=1)
    edges: List[Tuple[int, int]] = [(i, i + 1) for i in range(depth)]
    mid, s1, s2 = depth // 2, depth + 1, depth + 2
    edges.extend([(0, s1), (s1, mid), (mid, s2), (s2, depth)])
    for u, v in edges:
        tsh.add_entailment_edge(u, v)
        lsh.add_scalar_edge(u, v, 1, 1, 0)
    tsh.set_bounds(0, 0, 0)
    tsh.set_bounds(depth, 1, 1)
    lsh.pin_anchor(0, [0])
    lsh.pin_anchor(depth, [1])
    return tsh, lsh


def build_modus_tollens_contradiction(depth: int = 15, n_decoys: int = 20) -> Tuple[TarskiLatticeSheaf, List[int]]:
    bool_lat = BitmaskPowersetLattice(1)
    tsh = TarskiLatticeSheaf([bool_lat] * (depth + 1 + n_decoys))
    chain_eids = [tsh.add_entailment_edge(i, i + 1, label=f"chain_{i}->{i+1}") for i in range(depth)]
    for k in range(n_decoys):
        tsh.add_entailment_edge(depth + 1 + k, k % (depth + 1), label=f"decoy_{k}")
    tsh.set_bounds(0, 1, 1)
    tsh.set_bounds(depth, 0, 0)
    return tsh, chain_eids


def build_powerset_galois_sheaf(contradictory: bool = True) -> Tuple[TarskiLatticeSheaf, List[GaloisConnection]]:
    lat = BitmaskPowersetLattice(3)
    tsh = TarskiLatticeSheaf([lat, lat, lat])
    gc1 = GaloisConnection.from_relation_matrix(lat, lat, [0b011, 0b110, 0b100], label="R1")
    gc2 = GaloisConnection.from_relation_matrix(lat, lat, [0b001, 0b101, 0b110], label="R2")
    tsh.add_entailment_edge(0, 1, gc_u=gc1)
    tsh.add_entailment_edge(1, 2, gc_u=gc2)
    tsh.set_bounds(0, 0b001, 0b111)
    tsh.set_bounds(2, 0b000, 0b011 if contradictory else 0b101)
    return tsh, [gc1, gc2]


def build_caru_hardy_paradox() -> Tuple[SparseIntMatrix, List[int], List[int], List[int], List[int]]:
    A = SparseIntMatrix(5, 16)
    for idx in range(16):
        a0, a1, b0, b1 = (idx >> 3) & 1, (idx >> 2) & 1, (idx >> 1) & 1, idx & 1
        A.set_entry(0, idx, 1)
        if a0 == 0 and b0 == 0:
            A.set_entry(1, idx, 1)
        if a0 == 0 and b1 == 1:
            A.set_entry(2, idx, 1)
        if a1 == 1 and b0 == 0:
            A.set_entry(3, idx, 1)
        if a1 == 0 and b1 == 0:
            A.set_entry(4, idx, 1)
    c = [1, 1, 0, 0, 0]
    ghost = [0] * 16
    ghost[0b0000] = 1
    ghost[0b0010] = -1
    ghost[0b1111] = 1
    return A, c, [0] * 16, [1] * 16, ghost


def build_caru_elimination_ghost() -> Tuple[SparseIntMatrix, List[int], List[int], List[int], List[int]]:
    dense = [
        [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 1, 1, 0, 0, 0, 0, 0],
        [1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
        [0, 1, 0, 0, 1, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 1, 1, 0, 0],
        [0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
        [0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ]
    c = [1, 1, 2, 2, 1, 1, 1, 1]
    ghost = [1, 1, -1, 1, 1, 0, 1, 0, 0, 1]
    return SparseIntMatrix.from_dense(dense), c, [0] * 10, [1] * 10, ghost


def build_hybrid_order_algebraic_paradox() -> Tuple[
    SparseIntMatrix, List[int], List[int], List[int], List[DirectedIntInequality]
]:
    A = SparseIntMatrix.from_dense([[1, 1, 1]])
    return A, [1], [0, 0, 0], [1, 1, 1], [DirectedIntInequality(0, 1), DirectedIntInequality(1, 2), DirectedIntInequality(2, 0)]


def build_consistent_binary_hybrid_control() -> Tuple[
    SparseIntMatrix, List[int], List[int], List[int], List[DirectedIntInequality]
]:
    dense = [[1, 1, 1, 0, 0], [0, 1, 0, 1, 1], [1, 0, 0, 1, 0]]
    return (
        SparseIntMatrix.from_dense(dense),
        [2, 2, 1],
        [0] * 5,
        [1] * 5,
        [DirectedIntInequality(0, 1), DirectedIntInequality(3, 4)],
    )



# ==============================================================================
# v2.0 Red-Team Sophist Generators (Cycles 5 & 6):
#   - Class 6: Unpeelable 3-Regular Tseitin Expanders, Closed Surfaces & Moore Zoo
#   - Class 7: Quantum Contextuality (Mermin-Peres, GHZ, Cabello 18-Ray, KCBS CG)
# ==============================================================================


def _build_3regular_expander_matchings(N: int, seed: int = 20261119) -> List[List[Tuple[int, int]]]:
    """Build 3 edge-disjoint perfect matchings on even N >= 6 vertices -> 3-regular expander."""
    if N < 6 or N % 2 != 0:
        raise ValueError("N must be an even integer >= 6")
    rng = random.Random(seed)
    used_edges = set()
    matchings: List[List[Tuple[int, int]]] = []
    for _m_idx in range(3):
        for _attempt in range(200):
            verts = list(range(N))
            rng.shuffle(verts)
            cand: List[Tuple[int, int]] = []
            ok = True
            for i in range(0, N, 2):
                u, v = verts[i], verts[i + 1]
                key = (u, v) if u < v else (v, u)
                if key in used_edges:
                    ok = False
                    break
                cand.append((u, v))
            if ok:
                for u, v in cand:
                    used_edges.add((u, v) if u < v else (v, u))
                matchings.append(cand)
                break
        else:
            raise RuntimeError(f"Failed to build 3-regular expander matching for N={N}")
    return matchings


def build_unpeelable_tseitin_expander(
    N: int,
    modulus: int = 6,
    defect: int = 1,
    seed: int = 20261119,
) -> Tuple[SparseIntMatrix, List[int], int]:
    """Build a literal 0%-peelable 3-regular Tseitin mod-m charge expander B x = c.

    Uses 6 pairwise-distinct prime weights so exact SNF is [1,...,1,m], DHSW peels 0%,
    and float64/Q are 100% blind while v2.0 Double-Determinant compresses D_1 -> G <= 13 bits!
    """
    if modulus == 6:
        w_pairs = [(5, 7), (11, -17), (13, -19)]
    elif modulus == 2:
        w_pairs = [(3, -5), (7, -11), (13, -17)]
    elif modulus == 3:
        w_pairs = [(2, 4), (5, -2), (-7, 10)]
    else:
        raise ValueError(f"Unsupported expander modulus {modulus}; use 2, 3, or 6")

    matchings = _build_3regular_expander_matchings(N, seed=seed)
    n_edges = (3 * N) // 2
    B = SparseIntMatrix(N, n_edges)
    col = 0
    for m_idx, pairs in enumerate(matchings):
        wa, wb = w_pairs[m_idx]
        for u, v in pairs:
            B.set_entry(u, col, wa)
            B.set_entry(v, col, wb)
            col += 1

    c = [0] * N
    c[0] = defect
    return B, c, modulus


def build_torus_T2(defect: int = 1) -> Simplicial2Complex:
    """3x3 periodic triangulated Torus T^2 (9V, 27E, 18F, chi=0; H^1=Z^2, H^2=Z)."""
    cx = Simplicial2Complex(n_vertices=9)

    def vid(r: int, c: int) -> int:
        return (r % 3) * 3 + (c % 3)

    idx = 0
    for r in range(3):
        for c in range(3):
            v00, v01 = vid(r, c), vid(r, c + 1)
            v10, v11 = vid(r + 1, c), vid(r + 1, c + 1)
            cx.add_triangle(v00, v01, v11, rhs=(defect if idx == 0 else 0), label=f"T2_F{idx}")
            cx.add_triangle(v00, v11, v10, rhs=0, label=f"T2_F{idx+1}")
            idx += 2
    assert cx.verify_functoriality()
    return cx


def build_klein_bottle_K2(defect: int = 1) -> Simplicial2Complex:
    """3x3 triangulated Klein Bottle K^2 (9V, 27E, 18F, chi=0; H^1=Z, H^2=Z/2Z)."""
    cx = Simplicial2Complex(n_vertices=9)

    def vid(r: int, c: int) -> int:
        c = c % 3
        if r == 3:
            r = 0
            c = (3 - c) % 3
        return r * 3 + c

    idx = 0
    for r in range(3):
        for c in range(3):
            v00, v01 = vid(r, c), vid(r, c + 1)
            v10, v11 = vid(r + 1, c), vid(r + 1, c + 1)
            cx.add_triangle(v00, v01, v11, rhs=(defect if idx == 0 else 0), label=f"K2_F{idx}")
            cx.add_triangle(v00, v11, v10, rhs=0, label=f"K2_F{idx+1}")
            idx += 2
    assert cx.verify_functoriality()
    return cx


def build_simplicial_moore_space(m: int, defect: int = 1) -> Simplicial2Complex:
    """Pure {-1, 0, +1} triangulated 2D Moore Complex M(Z/mZ, 1) (H^1=0, H^2=Z/mZ)."""
    if m < 2:
        raise ValueError("m must be >= 2")
    L = 3 * m
    hub = 3 + L
    cx = Simplicial2Complex(n_vertices=hub + 1)

    def ring_v(k: int) -> int:
        return 3 + (k % L)

    def bdry_v(k: int) -> int:
        return k % 3

    idx = 0
    for k in range(L):
        rk, rk1 = ring_v(k), ring_v(k + 1)
        bk, bk1 = bdry_v(k), bdry_v(k + 1)
        cx.add_triangle(hub, rk, rk1, rhs=(defect if idx == 0 else 0), label=f"M{m}_cap_{k}")
        cx.add_triangle(rk1, rk, bk, rhs=0, label=f"M{m}_a1_{k}")
        cx.add_triangle(rk1, bk, bk1, rhs=0, label=f"M{m}_a2_{k}")
        idx += 3
    assert cx.verify_functoriality()
    return cx


def build_mermin_peres_magic_square() -> Tuple[SparseIntMatrix, List[int], List[int], List[int]]:
    """Mermin-Peres Magic Square (9 observables + 6 parity slacks -> Z_2 torsion, 0 branches)."""
    A = SparseIntMatrix(6, 15)
    c = [0, 0, 0, 0, 0, 1]
    for r in range(3):
        for col in range(3):
            A.set_entry(r, 3 * r + col, 1)
        A.set_entry(r, 9 + r, -2)
    for col in range(3):
        for r in range(3):
            A.set_entry(3 + col, 3 * r + col, 1)
        A.set_entry(3 + col, 12 + col, -2)
    return A, c, [0] * 15, [1] * 15


def build_ghz_3qubit_paradox() -> Tuple[SparseIntMatrix, List[int], List[int], List[int]]:
    """GHZ 3-Qubit Parity Paradox (6 observables + 4 parity slacks -> Z_2 torsion, 0 branches)."""
    A = SparseIntMatrix(4, 10)
    contexts = [(0, 1, 2), (0, 4, 5), (3, 1, 5), (3, 4, 2)]
    c = [0, 1, 1, 1]
    for r, (a, b, d) in enumerate(contexts):
        A.set_entry(r, a, 1)
        A.set_entry(r, b, 1)
        A.set_entry(r, d, 1)
        A.set_entry(r, 6 + r, -2)
    return A, c, [0] * 10, [1] * 10


def build_cabello_18ray_ks() -> Tuple[SparseIntMatrix, List[int], List[int], List[int]]:
    """Authentic 18-Vector Cabello Kochen-Specker Hypergraph (9 orthogonal tetrads -> Z_2 torsion)."""
    tetrads = [
        (0, 1, 2, 3), (0, 4, 5, 6), (1, 7, 8, 9),
        (2, 10, 11, 12), (3, 13, 14, 15), (4, 7, 10, 16),
        (5, 8, 13, 17), (6, 11, 14, 16), (9, 12, 15, 17),
    ]
    A = SparseIntMatrix(9, 18)
    for r, tet in enumerate(tetrads):
        for v in tet:
            A.set_entry(r, v, 1)
    return A, [1] * 9, [0] * 18, [1] * 18


def build_two_triangle_cg_ghost() -> Tuple[SparseIntMatrix, List[int], List[int], List[int]]:
    """18-Variable Strictly-Interior LP-Feasible 3-Triangle Chvatal-Gomory Ghost (0 branches!)."""
    A = SparseIntMatrix(10, 18)
    c = [1] * 9 + [4]
    for tri in range(3):
        base, s_base = 3 * tri, 9 + 3 * tri
        for p_idx, (a, b) in enumerate(((0, 1), (1, 2), (2, 0))):
            row = 3 * tri + p_idx
            A.set_entry(row, base + a, 1)
            A.set_entry(row, base + b, 1)
            A.set_entry(row, s_base + p_idx, 1)
    for j in range(9):
        A.set_entry(9, j, 1)
    return A, c, [0] * 18, [1] * 18


def build_coupled_kcbs_pentagon_cg_ghost() -> Tuple[SparseIntMatrix, List[int], List[int], List[int]]:
    """30-Variable Strictly-Interior LP-Feasible 3-Pentagon KCBS CG Ghost (0 branches!)."""
    A = SparseIntMatrix(16, 30)
    c = [1] * 15 + [7]
    for pent in range(3):
        base, s_base = 5 * pent, 15 + 5 * pent
        for i in range(5):
            row = 5 * pent + i
            A.set_entry(row, base + i, 1)
            A.set_entry(row, base + ((i + 1) % 5), 1)
            A.set_entry(row, s_base + i, 1)
    for j in range(15):
        A.set_entry(15, j, 1)
    return A, c, [0] * 30, [1] * 30


def build_high_nullity_hidden_cg_cut(
    extra_free_vars: int = 60, seed: int = 20261119
) -> Tuple[SparseIntMatrix, List[int], List[int], List[int]]:
    """Embed the 3-Triangle CG ghost inside `extra_free_vars` binary decoys (nu >= 40..80)."""
    rng = random.Random(seed)
    A0, c0, _, _ = build_two_triangle_cg_ghost()
    n0 = A0.ncols
    n_decoy_eqs = max(4, extra_free_vars // 5)
    total_vars = n0 + extra_free_vars
    A = SparseIntMatrix(A0.nrows + n_decoy_eqs, total_vars)
    c = list(c0)
    for r, rmap in A0.rows.items():
        for j, v in rmap.items():
            A.set_entry(r, j, v)
    x_decoy = [rng.randint(0, 1) for _ in range(extra_free_vars)]
    for k in range(n_decoy_eqs):
        chosen = rng.sample(range(n0, total_vars), 4)
        rhs = 0
        for j in chosen:
            A.set_entry(A0.nrows + k, j, 1)
            rhs += x_decoy[j - n0]
        c.append(rhs)
    return A, c, [0] * total_vars, [1] * total_vars


def build_high_nullity_planted_hard_open(
    n_vars: int = 64, n_eqs: int = 12, seed: int = 20261119
) -> Tuple[SparseIntMatrix, List[int], List[int], List[int]]:
    """High-nullity (nu >= 50) planted-SAT system testing sound 3-valued OPEN_BUDGET_EXCEEDED."""
    rng = random.Random(seed)
    A = SparseIntMatrix(n_eqs, n_vars)
    x_hidden = [1 if (i % 2 == 0) else 0 for i in range(n_vars)]
    rng.shuffle(x_hidden)
    ones = [i for i, v in enumerate(x_hidden) if v == 1]
    zeros = [i for i, v in enumerate(x_hidden) if v == 0]
    c: List[int] = []
    for r in range(n_eqs):
        for j in rng.sample(ones, 3) + rng.sample(zeros, 3):
            A.set_entry(r, j, 1)
        c.append(3)
    return A, c, [0] * n_vars, [1] * n_vars
