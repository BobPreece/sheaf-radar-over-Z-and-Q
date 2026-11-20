"""Cellular 1-Complex & Simplicial 2-Complex Exact Sheaf Cohomology and Torsor Engine.

Provides:
- CellularSheaf1Complex: arbitrary vector/module stalks over Z or Q, relative anchor
  vertices v_*, Guardrail B separation (no scaling over Z; row-LCM clearing over Q).
- Simplicial2Complex: exact cochain complex C^0 -> C^1 -> C^2 asserting
  delta^1 @ delta^0 == 0 identically over Z, SNF cohomology H^0, H^1, H^2, and
  inhomogeneous H^2 multi-premise torsor solvability delta^1 y = d.

Strictly Python 3 stdlib only. Zero fractions.Fraction usage.
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple, Union

from .sparse_exact import (
    SNFResult,
    SparseIntMatrix,
    TorsorResult,
    compute_snf,
    solve_torsor,
)

Rat = Tuple[int, int]
IntOrRat = Union[int, Rat]


@dataclass
class SheafEdge1D:
    edge_id: int
    u: int
    v: int
    stalk_dim: int
    F_u: List[List[IntOrRat]]
    F_v: List[List[IntOrRat]]
    c_e: List[IntOrRat]
    label: str = ""


@dataclass
class Cohomology1Report:
    ring: str
    n_vertices: int
    n_edges: int
    dim_C0: int
    dim_C1: int
    rank_delta0: int
    beta_0: int
    beta_1: int
    torsion_h1: List[int]
    snf_invariant_factors: List[int]
    max_bits: int

    def format_h1(self) -> str:
        parts: List[str] = []
        if self.beta_1 > 0:
            sym = "Z" if self.ring == "Z" else "Q"
            parts.append(f"{sym}^{self.beta_1}" if self.beta_1 > 1 else sym)
        if self.ring == "Z":
            for d in self.torsion_h1:
                parts.append(f"Z/{d}Z")
        return " (+) ".join(parts) if parts else "0"


class CellularSheaf1Complex:
    """Exact cellular sheaf & affine torsor over a 1-dimensional cell complex (graph)."""

    def __init__(self, ring: str = "Z") -> None:
        if ring not in ("Z", "Q"):
            raise ValueError(f"ring must be 'Z' or 'Q', got {ring!r}")
        self.ring = ring
        self.vertex_dims: List[int] = []
        self.vertex_offsets: List[int] = []
        self.total_c0: int = 0
        self.edges: List[SheafEdge1D] = []
        self.anchors: List[Tuple[int, List[IntOrRat]]] = []

    def add_vertex(self, stalk_dim: int = 1) -> int:
        if stalk_dim <= 0:
            raise ValueError("stalk_dim must be >= 1")
        vid = len(self.vertex_dims)
        self.vertex_dims.append(stalk_dim)
        self.vertex_offsets.append(self.total_c0)
        self.total_c0 += stalk_dim
        return vid

    def add_vertices(self, count: int, stalk_dim: int = 1) -> List[int]:
        return [self.add_vertex(stalk_dim) for _ in range(count)]

    def add_edge(
        self,
        u: int,
        v: int,
        F_u: Sequence[Sequence[IntOrRat]],
        F_v: Sequence[Sequence[IntOrRat]],
        c_e: Optional[Sequence[IntOrRat]] = None,
        label: str = "",
    ) -> int:
        if not (0 <= u < len(self.vertex_dims) and 0 <= v < len(self.vertex_dims)):
            raise IndexError(f"Vertex out of range: u={u}, v={v}")
        d_e = len(F_u)
        if len(F_v) != d_e:
            raise ValueError(f"F_u rows ({d_e}) != F_v rows ({len(F_v)})")
        du, dv = self.vertex_dims[u], self.vertex_dims[v]
        for row in F_u:
            if len(row) != du:
                raise ValueError(f"F_u col mismatch: expected {du}, got {len(row)}")
        for row in F_v:
            if len(row) != dv:
                raise ValueError(f"F_v col mismatch: expected {dv}, got {len(row)}")
        if c_e is None:
            rhs_e: List[IntOrRat] = [0] * d_e if self.ring == "Z" else [(0, 1)] * d_e
        else:
            if len(c_e) != d_e:
                raise ValueError(f"c_e length ({len(c_e)}) != d_e ({d_e})")
            rhs_e = list(c_e)

        if self.ring == "Z":
            for blk in (F_u, F_v):
                for row in blk:
                    for val in row:
                        if isinstance(val, tuple) and val[1] != 1:
                            raise ValueError(
                                f"Guardrail B violation: non-integral rational {val} in Z-sheaf!"
                            )
            for val in rhs_e:
                if isinstance(val, tuple) and val[1] != 1:
                    raise ValueError(
                        f"Guardrail B violation: non-integral RHS {val} in Z-sheaf!"
                    )

        eid = len(self.edges)
        self.edges.append(
            SheafEdge1D(
                edge_id=eid,
                u=u,
                v=v,
                stalk_dim=d_e,
                F_u=[list(r) for r in F_u],
                F_v=[list(r) for r in F_v],
                c_e=rhs_e,
                label=label or f"e{eid}({u}->{v})",
            )
        )
        return eid

    def add_scalar_edge(
        self,
        u: int,
        v: int,
        coeff_u: IntOrRat,
        coeff_v: IntOrRat,
        rhs: IntOrRat = 0,
        label: str = "",
    ) -> int:
        return self.add_edge(u, v, [[coeff_u]], [[coeff_v]], [rhs], label=label)

    def pin_anchor(self, vertex_id: int, value: Sequence[IntOrRat]) -> None:
        if not (0 <= vertex_id < len(self.vertex_dims)):
            raise IndexError(f"Invalid anchor vertex {vertex_id}")
        if len(value) != self.vertex_dims[vertex_id]:
            raise ValueError("Anchor value dimension mismatch")
        if self.ring == "Z":
            for val in value:
                if isinstance(val, tuple) and val[1] != 1:
                    raise ValueError("Guardrail B violation: rational anchor in Z-sheaf")
        self.anchors.append((vertex_id, list(value)))

    @staticmethod
    def _to_int(val: IntOrRat) -> int:
        if isinstance(val, tuple):
            num, den = val
            if den == 1:
                return int(num)
            if den == -1:
                return -int(num)
            raise ValueError(f"Expected integer, got {val}")
        return int(val)

    @staticmethod
    def _to_rat(val: IntOrRat) -> Rat:
        if isinstance(val, tuple):
            return (int(val[0]), int(val[1]))
        return (int(val), 1)

    def build_coboundary(
        self,
        edge_subset: Optional[Sequence[int]] = None,
        include_anchors: bool = True,
    ) -> Tuple[SparseIntMatrix, List[int], List[int]]:
        selected_edges = (
            [self.edges[eid] for eid in edge_subset]
            if edge_subset is not None
            else self.edges
        )
        n_rows = sum(e.stalk_dim for e in selected_edges)
        if include_anchors:
            n_rows += sum(len(val) for _, val in self.anchors)
        n_cols = self.total_c0
        row_to_cell: List[int] = []

        if self.ring == "Z":
            A = SparseIntMatrix(n_rows, n_cols)
            c_vec = [0] * n_rows
            r_cursor = 0
            for e in selected_edges:
                off_u = self.vertex_offsets[e.u]
                off_v = self.vertex_offsets[e.v]
                du = self.vertex_dims[e.u]
                dv = self.vertex_dims[e.v]
                for i in range(e.stalk_dim):
                    for j in range(du):
                        val = self._to_int(e.F_u[i][j])
                        if val != 0:
                            A.add_entry(r_cursor, off_u + j, -val)
                    for j in range(dv):
                        val = self._to_int(e.F_v[i][j])
                        if val != 0:
                            A.add_entry(r_cursor, off_v + j, val)
                    c_vec[r_cursor] = self._to_int(e.c_e[i])
                    row_to_cell.append(e.edge_id)
                    r_cursor += 1
            if include_anchors:
                for a_idx, (vid, aval) in enumerate(self.anchors):
                    off_v = self.vertex_offsets[vid]
                    for j, val in enumerate(aval):
                        A.set_entry(r_cursor, off_v + j, 1)
                        c_vec[r_cursor] = self._to_int(val)
                        row_to_cell.append(-1 - a_idx)
                        r_cursor += 1
            return A, c_vec, row_to_cell

        rat_entries: List[Tuple[int, int, int, int]] = []
        rat_rhs: List[Rat] = []
        r_cursor = 0
        for e in selected_edges:
            off_u = self.vertex_offsets[e.u]
            off_v = self.vertex_offsets[e.v]
            du = self.vertex_dims[e.u]
            dv = self.vertex_dims[e.v]
            for i in range(e.stalk_dim):
                for j in range(du):
                    num, den = self._to_rat(e.F_u[i][j])
                    if num != 0:
                        rat_entries.append((r_cursor, off_u + j, -num, den))
                for j in range(dv):
                    num, den = self._to_rat(e.F_v[i][j])
                    if num != 0:
                        rat_entries.append((r_cursor, off_v + j, num, den))
                rat_rhs.append(self._to_rat(e.c_e[i]))
                row_to_cell.append(e.edge_id)
                r_cursor += 1
        if include_anchors:
            for a_idx, (vid, aval) in enumerate(self.anchors):
                off_v = self.vertex_offsets[vid]
                for j, val in enumerate(aval):
                    rat_entries.append((r_cursor, off_v + j, 1, 1))
                    rat_rhs.append(self._to_rat(val))
                    row_to_cell.append(-1 - a_idx)
                    r_cursor += 1

        A, c_vec = SparseIntMatrix.from_rational_rows(n_rows, n_cols, rat_entries, rat_rhs)
        return A, c_vec, row_to_cell

    def build_float64_coboundary(
        self,
        edge_subset: Optional[Sequence[int]] = None,
        include_anchors: bool = True,
    ) -> Tuple[List[List[float]], List[float]]:
        selected_edges = (
            [self.edges[eid] for eid in edge_subset]
            if edge_subset is not None
            else self.edges
        )
        n_rows = sum(e.stalk_dim for e in selected_edges)
        if include_anchors:
            n_rows += sum(len(val) for _, val in self.anchors)
        n_cols = self.total_c0
        mat = [[0.0] * n_cols for _ in range(n_rows)]
        rhs = [0.0] * n_rows

        def to_f(val: IntOrRat) -> float:
            if isinstance(val, tuple):
                return float(val[0]) / float(val[1])
            return float(val)

        r_cursor = 0
        for e in selected_edges:
            off_u = self.vertex_offsets[e.u]
            off_v = self.vertex_offsets[e.v]
            du = self.vertex_dims[e.u]
            dv = self.vertex_dims[e.v]
            for i in range(e.stalk_dim):
                row = mat[r_cursor]
                for j in range(du):
                    fv = to_f(e.F_u[i][j])
                    if fv != 0.0:
                        row[off_u + j] -= fv
                for j in range(dv):
                    fv = to_f(e.F_v[i][j])
                    if fv != 0.0:
                        row[off_v + j] += fv
                rhs[r_cursor] = to_f(e.c_e[i])
                r_cursor += 1
        if include_anchors:
            for vid, aval in self.anchors:
                off_v = self.vertex_offsets[vid]
                for j, val in enumerate(aval):
                    mat[r_cursor][off_v + j] = 1.0
                    rhs[r_cursor] = to_f(val)
                    r_cursor += 1
        return mat, rhs

    def compute_cohomology(self, include_anchors: bool = False) -> Cohomology1Report:
        A, _, _ = self.build_coboundary(include_anchors=include_anchors)
        if self.ring == "Z":
            snf: SNFResult = compute_snf(A)
            rank, torsion, inv, mb = snf.rank, snf.torsion_factors, snf.invariant_factors, snf.max_bits
        else:
            res = solve_torsor(A, [0] * A.nrows, ring="Q", want_witness=False)
            rank, torsion, inv, mb = res.rank_q, [], [1] * res.rank_q, res.max_bits
        return Cohomology1Report(
            ring=self.ring,
            n_vertices=len(self.vertex_dims),
            n_edges=len(self.edges),
            dim_C0=A.ncols,
            dim_C1=A.nrows,
            rank_delta0=rank,
            beta_0=A.ncols - rank,
            beta_1=A.nrows - rank,
            torsion_h1=torsion,
            snf_invariant_factors=inv,
            max_bits=mb,
        )

    def solve_affine_torsor(
        self,
        edge_subset: Optional[Sequence[int]] = None,
        include_anchors: bool = True,
        want_witness: bool = True,
    ) -> Tuple[TorsorResult, SparseIntMatrix, List[int]]:
        A, c_vec, _ = self.build_coboundary(
            edge_subset=edge_subset, include_anchors=include_anchors
        )
        res = solve_torsor(A, c_vec, ring=self.ring, want_witness=want_witness)
        return res, A, c_vec


@dataclass
class Face2Cell:
    face_id: int
    boundary_edges: List[Tuple[int, int]]
    vertices: Tuple[int, ...]
    rhs: int = 0
    label: str = ""


@dataclass
class Cohomology2Report:
    ring: str
    n_vertices: int
    n_edges: int
    n_faces: int
    functoriality_verified: bool
    rank_delta0: int
    rank_delta1: int
    beta_0: int
    beta_1: int
    beta_2: int
    torsion_h1: List[int]
    torsion_h2: List[int]
    snf_delta0: List[int]
    snf_delta1: List[int]
    euler_characteristic: int
    max_bits: int

    def _fmt_group(self, beta: int, torsion: List[int]) -> str:
        parts: List[str] = []
        sym = "Z" if self.ring == "Z" else "Q"
        if beta > 0:
            parts.append(f"{sym}^{beta}" if beta > 1 else sym)
        if self.ring == "Z":
            for d in torsion:
                parts.append(f"Z/{d}Z")
        return " (+) ".join(parts) if parts else "0"

    def format_h0(self) -> str:
        return self._fmt_group(self.beta_0, [])

    def format_h1(self) -> str:
        return self._fmt_group(self.beta_1, self.torsion_h1)

    def format_h2(self) -> str:
        return self._fmt_group(self.beta_2, self.torsion_h2)


class Simplicial2Complex:
    """Exact simplicial / cellular 2-complex over Z or Q."""

    def __init__(self, n_vertices: int = 0) -> None:
        self.n_vertices: int = n_vertices
        self.edges: List[Tuple[int, int]] = []
        self.edge_index: Dict[Tuple[int, int], int] = {}
        self.edge_rhs: List[int] = []
        self.faces: List[Face2Cell] = []

    def add_vertices(self, count: int) -> List[int]:
        start = self.n_vertices
        self.n_vertices += count
        return list(range(start, self.n_vertices))

    def get_or_add_edge(self, u: int, v: int, rhs: int = 0) -> Tuple[int, int]:
        if u == v:
            raise ValueError("Self-loop not allowed in simplicial 2-complex")
        if max(u, v) >= self.n_vertices:
            self.n_vertices = max(u, v) + 1
        key, sign = ((u, v), 1) if u < v else ((v, u), -1)
        eid = self.edge_index.get(key)
        if eid is None:
            eid = len(self.edges)
            self.edges.append(key)
            self.edge_index[key] = eid
            self.edge_rhs.append(rhs * sign)
        return eid, sign

    def add_triangle(self, u: int, v: int, w: int, rhs: int = 0, label: str = "") -> int:
        if len({u, v, w}) != 3:
            raise ValueError(f"Degenerate triangle ({u}, {v}, {w})")
        verts = [u, v, w]
        inv_count = sum(1 for i in range(3) for j in range(i + 1, 3) if verts[i] > verts[j])
        orient = -1 if (inv_count & 1) else 1
        a, b, c = sorted(verts)
        e_ab, _ = self.get_or_add_edge(a, b)
        e_bc, _ = self.get_or_add_edge(b, c)
        e_ac, _ = self.get_or_add_edge(a, c)
        boundary = [(e_bc, orient), (e_ac, -orient), (e_ab, orient)]
        fid = len(self.faces)
        self.faces.append(
            Face2Cell(
                face_id=fid,
                boundary_edges=boundary,
                vertices=(u, v, w),
                rhs=rhs,
                label=label or f"F{fid}({u},{v},{w})",
            )
        )
        return fid

    def build_delta0(self) -> SparseIntMatrix:
        D0 = SparseIntMatrix(len(self.edges), self.n_vertices)
        for eid, (u, v) in enumerate(self.edges):
            D0.set_entry(eid, u, -1)
            D0.set_entry(eid, v, 1)
        return D0

    def build_delta1(self, face_subset: Optional[Sequence[int]] = None) -> Tuple[SparseIntMatrix, List[int]]:
        sel_faces = [self.faces[fid] for fid in face_subset] if face_subset is not None else self.faces
        D1 = SparseIntMatrix(len(sel_faces), len(self.edges))
        d_vec = [0] * len(sel_faces)
        for r_idx, face in enumerate(sel_faces):
            for eid, sign in face.boundary_edges:
                D1.add_entry(r_idx, eid, sign)
            d_vec[r_idx] = face.rhs
        return D1, d_vec

    def verify_functoriality(self) -> bool:
        D0 = self.build_delta0()
        D1, _ = self.build_delta1()
        return D1.matmul(D0).is_zero()

    def compute_cohomology(self, ring: str = "Z") -> Cohomology2Report:
        if ring not in ("Z", "Q"):
            raise ValueError(f"ring must be 'Z' or 'Q', got {ring!r}")
        D0 = self.build_delta0()
        D1, _ = self.build_delta1()
        assert D1.matmul(D0).is_zero(), "Functoriality violation: delta^1 @ delta^0 != 0 over Z!"
        if ring == "Z":
            snf0, snf1 = compute_snf(D0), compute_snf(D1)
            r0, r1 = snf0.rank, snf1.rank
            t1, t2 = snf0.torsion_factors, snf1.torsion_factors
            inv0, inv1 = snf0.invariant_factors, snf1.invariant_factors
            mb = max(snf0.max_bits, snf1.max_bits)
        else:
            res0 = solve_torsor(D0, [0] * D0.nrows, ring="Q", want_witness=False)
            res1 = solve_torsor(D1, [0] * D1.nrows, ring="Q", want_witness=False)
            r0, r1 = res0.rank_q, res1.rank_q
            t1, t2 = [], []
            inv0, inv1 = [1] * r0, [1] * r1
            mb = max(res0.max_bits, res1.max_bits)

        n0, n1, n2 = self.n_vertices, len(self.edges), len(self.faces)
        b0, b1, b2 = n0 - r0, n1 - r0 - r1, n2 - r1
        chi = n0 - n1 + n2
        assert chi == b0 - b1 + b2
        return Cohomology2Report(
            ring=ring,
            n_vertices=n0,
            n_edges=n1,
            n_faces=n2,
            functoriality_verified=True,
            rank_delta0=r0,
            rank_delta1=r1,
            beta_0=b0,
            beta_1=b1,
            beta_2=b2,
            torsion_h1=t1,
            torsion_h2=t2,
            snf_delta0=inv0,
            snf_delta1=inv1,
            euler_characteristic=chi,
            max_bits=mb,
        )

    def solve_h2_torsor(
        self,
        ring: str = "Z",
        face_subset: Optional[Sequence[int]] = None,
        want_witness: bool = True,
    ) -> Tuple[TorsorResult, SparseIntMatrix, List[int]]:
        D1, d_vec = self.build_delta1(face_subset=face_subset)
        res = solve_torsor(D1, d_vec, ring=ring, want_witness=want_witness)
        return res, D1, d_vec
