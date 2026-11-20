#!/usr/bin/env python3
"""standalone_sheaf_contradiction_radar.py (v2.0.0) — Zero-Dependency Exact Z/Q Cellular Sheaf,
Double-Determinant Expander Compression, Chvatal-Gomory Contextuality Closure,
Streaming Pre-Commit Sheaf Firewall & 5-Domain Forensic Claim Compiler.

Author: Bob Preece (2026), MIT License.
Strictly Python 3 standard library only (zero NumPy/SciPy/SymPy/fractions).
Deterministic verification seed: 20261119.

Usage:
    python3 standalone_sheaf_contradiction_radar.py
"""

from collections import deque
from dataclasses import dataclass, field
import json
import math
from pathlib import Path
import random
import sys
import time
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

__version__ = "2.0.0"
se = sys.modules[__name__]
fb = sys.modules[__name__]
th2 = sys.modules[__name__]



# ==============================================================================
# SECTION 1: EXACT SPARSE Z/Q LINEAR ALGEBRA v2.0 (CRT, DOUBLE-DET, DIGIT-SNF)
# ==============================================================================

# 20 verified distinct 61-bit primes (product > 2^1219)
CRT_PRIMES_61: List[int] = [
    (1 << 61) - 1,    # 2305843009213693951 (Mersenne prime)
    (1 << 61) - 31,   # 2305843009213693921
    (1 << 61) - 45,   # 2305843009213693907
    (1 << 61) - 229,  # 2305843009213693723
    (1 << 61) - 259,  # 2305843009213693693
    (1 << 61) - 283,  # 2305843009213693669
    (1 << 61) - 339,  # 2305843009213693613
    (1 << 61) - 391,  # 2305843009213693561
    (1 << 61) - 403,  # 2305843009213693549
    (1 << 61) - 465,  # 2305843009213693487
    (1 << 61) - 531,  # 2305843009213693421
    (1 << 61) - 579,  # 2305843009213693373
    (1 << 61) - 675,  # 2305843009213693277
    (1 << 61) - 759,  # 2305843009213693193
    (1 << 61) - 799,  # 2305843009213693153
    (1 << 61) - 819,  # 2305843009213693133
    (1 << 61) - 829,  # 2305843009213693123
    (1 << 61) - 843,  # 2305843009213693109
    (1 << 61) - 859,  # 2305843009213693093
    (1 << 61) - 939,  # 2305843009213693013
]

PRIME_1 = CRT_PRIMES_61[0]
PRIME_2 = CRT_PRIMES_61[1]


def _is_probable_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for all n < 3.317e24 (exact for all 61-bit and 64-bit ints)."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while (d & 1) == 0:
        d >>= 1
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _get_crt_primes(count: int) -> List[int]:
    """Return `count` distinct 61-bit primes, extending CRT_PRIMES_61 dynamically if needed."""
    if count <= len(CRT_PRIMES_61):
        return CRT_PRIMES_61[:count]
    cand = CRT_PRIMES_61[-1] - 2
    while len(CRT_PRIMES_61) < count:
        if _is_probable_prime(cand):
            CRT_PRIMES_61.append(cand)
        cand -= 2
    return CRT_PRIMES_61[:count]


def xgcd(a: int, b: int) -> Tuple[int, int, int]:
    """Extended Euclidean algorithm returning (g, s, t) with g >= 0 and s*a + t*b == g."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def _gcd_values(vals: Iterable[int]) -> int:
    g = 0
    for v in vals:
        g = math.gcd(g, v)
        if g == 1:
            return 1
    return g


def _pollard_rho(n: int, max_steps: int = 4000) -> Optional[int]:
    if (n & 1) == 0:
        return 2
    for c in (1, 3, 5, 7, 11):
        x = 2
        y = 2
        d = 1
        steps = 0
        while d == 1 and steps < max_steps:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
            steps += 1
        if 1 < d < n:
            return d
    return None


def factor_prime_powers(n: int) -> Optional[List[Tuple[int, int]]]:
    """Factor positive integer n into [(p, e), ...] with p prime.
    Returns None only if an unfactorable cofactor > 2^64 exceeds Pollard-rho step budget.
    """
    if n <= 1:
        return []
    factors: Dict[int, int] = {}
    rem = n
    # Fast trial division up to 10,000
    while (rem & 1) == 0:
        factors[2] = factors.get(2, 0) + 1
        rem >>= 1
    d = 3
    while d * d <= rem and d <= 10000:
        if rem % d == 0:
            cnt = 0
            while rem % d == 0:
                rem //= d
                cnt += 1
            factors[d] = factors.get(d, 0) + cnt
        d += 2

    stack = [rem] if rem > 1 else []
    while stack:
        cur = stack.pop()
        if cur <= 1:
            continue
        if _is_probable_prime(cur):
            factors[cur] = factors.get(cur, 0) + 1
            continue
        if cur.bit_length() > 80:
            return None
        div = _pollard_rho(cur)
        if div is None:
            return None
        stack.append(div)
        stack.append(cur // div)

    return sorted(factors.items())


def _perm_sign(perm: Sequence[int]) -> int:
    """Compute sign (+1 or -1) of a permutation of 0..n-1 in O(n) via cycle parity."""
    n = len(perm)
    visited = [False] * n
    swaps = 0
    for i in range(n):
        if visited[i]:
            continue
        cur = i
        cycle_len = 0
        while not visited[cur]:
            visited[cur] = True
            cur = perm[cur]
            cycle_len += 1
        if cycle_len > 1:
            swaps += cycle_len - 1
    return -1 if (swaps & 1) else 1


class SparseIntMatrix:
    """Native arbitrary-precision Python int sparse matrix with row maps and col incidence sets."""

    __slots__ = ("nrows", "ncols", "rows", "cols")

    def __init__(self, nrows: int, ncols: int) -> None:
        self.nrows = nrows
        self.ncols = ncols
        self.rows: Dict[int, Dict[int, int]] = {}
        self.cols: Dict[int, Set[int]] = {}

    def set_entry(self, r: int, c: int, val: int) -> None:
        if not (0 <= r < self.nrows and 0 <= c < self.ncols):
            raise IndexError(f"Index ({r}, {c}) out of bounds for ({self.nrows}, {self.ncols})")
        if val == 0:
            row = self.rows.get(r)
            if row is not None and c in row:
                del row[c]
                if not row:
                    del self.rows[r]
                col = self.cols.get(c)
                if col is not None:
                    col.discard(r)
                    if not col:
                        del self.cols[c]
            return
        row = self.rows.get(r)
        if row is None:
            row = {}
            self.rows[r] = row
        row[c] = val
        col = self.cols.get(c)
        if col is None:
            col = set()
            self.cols[c] = col
        col.add(r)

    def add_entry(self, r: int, c: int, delta: int) -> None:
        if delta == 0:
            return
        self.set_entry(r, c, self.get_entry(r, c) + delta)

    def get_entry(self, r: int, c: int) -> int:
        row = self.rows.get(r)
        return 0 if row is None else row.get(c, 0)

    def copy(self) -> "SparseIntMatrix":
        m = SparseIntMatrix(self.nrows, self.ncols)
        for r, row in self.rows.items():
            m.rows[r] = dict(row)
        for c, col in self.cols.items():
            m.cols[c] = set(col)
        return m

    def nnz(self) -> int:
        return sum(len(row) for row in self.rows.values())

    def max_bit_length(self) -> int:
        mx = 0
        for row in self.rows.values():
            for v in row.values():
                bl = abs(v).bit_length()
                if bl > mx:
                    mx = bl
        return mx

    def transpose(self) -> "SparseIntMatrix":
        t = SparseIntMatrix(self.ncols, self.nrows)
        for r, row in self.rows.items():
            for c, v in row.items():
                t.set_entry(c, r, v)
        return t

    def matvec(self, x: Sequence[int]) -> List[int]:
        if len(x) != self.ncols:
            raise ValueError(f"Expected vector length {self.ncols}, got {len(x)}")
        out = [0] * self.nrows
        for r, row in self.rows.items():
            acc = 0
            for c, v in row.items():
                xv = x[c]
                if xv:
                    acc += v * xv
            out[r] = acc
        return out

    def matmul(self, other: "SparseIntMatrix") -> "SparseIntMatrix":
        if self.ncols != other.nrows:
            raise ValueError(f"Dimension mismatch: ({self.nrows},{self.ncols}) @ ({other.nrows},{other.ncols})")
        res = SparseIntMatrix(self.nrows, other.ncols)
        for r, row_a in self.rows.items():
            acc: Dict[int, int] = {}
            for k, av in row_a.items():
                row_b = other.rows.get(k)
                if not row_b:
                    continue
                for c, bv in row_b.items():
                    nv = acc.get(c, 0) + av * bv
                    if nv == 0:
                        acc.pop(c, None)
                    else:
                        acc[c] = nv
            if acc:
                res.rows[r] = acc
                for c in acc:
                    res.cols.setdefault(c, set()).add(r)
        return res

    def is_zero(self) -> bool:
        return len(self.rows) == 0

    def row_subset(self, row_indices: Sequence[int]) -> "SparseIntMatrix":
        sub = SparseIntMatrix(len(row_indices), self.ncols)
        for new_r, old_r in enumerate(row_indices):
            row = self.rows.get(old_r)
            if row:
                sub.rows[new_r] = dict(row)
                for c in row:
                    sub.cols.setdefault(c, set()).add(new_r)
        return sub

    def to_dense(self) -> List[List[int]]:
        mat = [[0] * self.ncols for _ in range(self.nrows)]
        for r, row in self.rows.items():
            target = mat[r]
            for c, v in row.items():
                target[c] = v
        return mat

    @classmethod
    def from_dense(cls, mat: Sequence[Sequence[int]]) -> "SparseIntMatrix":
        nrows = len(mat)
        ncols = len(mat[0]) if nrows > 0 else 0
        m = cls(nrows, ncols)
        for r, row in enumerate(mat):
            for c, v in enumerate(row):
                if v != 0:
                    m.set_entry(r, c, int(v))
        return m

    @classmethod
    def from_rational_rows(
        cls,
        nrows: int,
        ncols: int,
        rational_entries: Sequence[Tuple[int, int, int, int]],
        rational_rhs: Optional[Sequence[Tuple[int, int]]] = None,
    ) -> Tuple["SparseIntMatrix", List[int]]:
        """Guardrail B: Strictly for Q-sheaves. Clears row denominators via row-wise LCM."""
        row_data: Dict[int, Dict[int, Tuple[int, int]]] = {}
        row_lcm: List[int] = [1] * nrows
        for r, c, num, den in rational_entries:
            if den == 0:
                raise ZeroDivisionError("Zero denominator in rational entry")
            if den < 0:
                num, den = -num, -den
            if num == 0:
                continue
            g = math.gcd(abs(num), den)
            num //= g
            den //= g
            rd = row_data.setdefault(r, {})
            if c in rd:
                p_num, p_den = rd[c]
                n_num = p_num * den + num * p_den
                n_den = p_den * den
                if n_num == 0:
                    del rd[c]
                else:
                    gg = math.gcd(abs(n_num), n_den)
                    rd[c] = (n_num // gg, n_den // gg)
            else:
                rd[c] = (num, den)
        for r, rd in row_data.items():
            lval = 1
            for _, den in rd.values():
                lval = math.lcm(lval, den)
            row_lcm[r] = lval
        c_int = [0] * nrows
        if rational_rhs is not None:
            for r, (num, den) in enumerate(rational_rhs):
                if den == 0:
                    raise ZeroDivisionError("Zero denominator in rational RHS")
                if den < 0:
                    num, den = -num, -den
                if num != 0:
                    g = math.gcd(abs(num), den)
                    row_lcm[r] = math.lcm(row_lcm[r], den // g)
        A = cls(nrows, ncols)
        for r in range(nrows):
            lval = row_lcm[r]
            rd = row_data.get(r)
            if rd:
                for c, (num, den) in rd.items():
                    A.set_entry(r, c, num * (lval // den))
            if rational_rhs is not None:
                num, den = rational_rhs[r]
                if den < 0:
                    num, den = -num, -den
                if num != 0:
                    g = math.gcd(abs(num), den)
                    c_int[r] = (num // g) * (lval // (den // g))
            row = A.rows.get(r)
            if row:
                g = _gcd_values(row.values())
                if c_int[r] != 0:
                    g = math.gcd(g, abs(c_int[r]))
                if g > 1:
                    for c in list(row.keys()):
                        row[c] //= g
                    c_int[r] //= g
        return A, c_int


@dataclass
class TorsorResult:
    status: str  # "SAT_INTEGRAL", "SAT_Q", "UNSAT_TORSION", "UNSAT_FREE_COHOMOLOGY"
    ring: str
    rank_q: int
    peeled_rank: int
    core_shape: Tuple[int, int]
    max_bits: int
    x_int: Optional[List[int]] = None
    x_q_num: Optional[List[int]] = None
    x_q_den: int = 1
    dual_free_witness: Optional[Dict[int, int]] = None
    torsion_cert: Optional[Tuple[int, int]] = None
    dual_torsion_witness: Optional[Tuple[Dict[int, int], int]] = None
    pivot_rows_core: List[int] = field(default_factory=list)
    pivot_cols_core: List[int] = field(default_factory=list)
    prescreen_agreed: bool = True
    double_det_G: Optional[int] = None
    single_det_D1_bits: Optional[int] = None


@dataclass
class PeelingOutcome:
    unsat_free: bool
    empty_contradiction_row: Optional[int]
    peeled_rank: int
    core_matrix: SparseIntMatrix
    core_rhs: List[int]
    core_orig_rows: List[int]
    core_orig_cols: List[int]
    backsub_stack: List[Tuple[int, int, Dict[int, int], int]]
    ops_log: List[Tuple[int, int, int]]
    max_bits: int


def dhsw_peel_torsor(
    A: SparseIntMatrix,
    c: Sequence[int],
    max_markowitz: int = 4,
    max_bits_fill: int = 48,
    max_bits_chain: int = 256,
    record_ops: bool = True,
) -> PeelingOutcome:
    """Strictly unimodular DHSW +/-1 unit-pivot, degree-1 leaf & O(E log V) degree-2 contraction."""
    nrows, ncols = A.nrows, A.ncols
    rows: Dict[int, Dict[int, int]] = {r: dict(row) for r, row in A.rows.items()}
    cols: Dict[int, Set[int]] = {j: set(col) for j, col in A.cols.items()}
    rhs: List[int] = list(c)
    active_rows: Set[int] = set(range(nrows))
    active_cols: Set[int] = set(range(ncols))

    max_bits = max(A.max_bit_length(), max((abs(v).bit_length() for v in rhs), default=0))
    backsub_stack: List[Tuple[int, int, Dict[int, int], int]] = []
    ops_log: List[Tuple[int, int, int]] = []
    peeled_rank = 0

    for r in list(active_rows):
        if r not in rows or not rows[r]:
            if rhs[r] != 0:
                return PeelingOutcome(True, r, 0, SparseIntMatrix(0, 0), [], [], [], [], [], max_bits)
            active_rows.discard(r)
    for j in list(active_cols):
        if j not in cols or not cols[j]:
            active_cols.discard(j)

    row_deg1: deque = deque()
    col_deg1: deque = deque()
    row_deg2: deque = deque()
    for r in active_rows:
        lr = len(rows[r])
        if lr == 1:
            row_deg1.append(r)
        elif lr == 2:
            row_deg2.append(r)
    for j in active_cols:
        if len(cols[j]) == 1:
            col_deg1.append(j)

    def eliminate_unit_pivot(r_piv: int, j_piv: int) -> Optional[int]:
        nonlocal peeled_rank, max_bits
        piv_val = rows[r_piv][j_piv]
        other_rows = [r2 for r2 in cols[j_piv] if r2 != r_piv]
        piv_row = rows[r_piv]
        c_piv = rhs[r_piv]
        for r2 in other_rows:
            r2_map = rows[r2]
            v = r2_map[j_piv]
            factor = v * piv_val
            if record_ops:
                ops_log.append((r2, r_piv, factor))
            new_rhs = rhs[r2] - factor * c_piv
            rhs[r2] = new_rhs
            bl = abs(new_rhs).bit_length()
            if bl > max_bits:
                max_bits = bl
            for col_k, pv in piv_row.items():
                nv = r2_map.get(col_k, 0) - factor * pv
                if nv == 0:
                    if col_k in r2_map:
                        del r2_map[col_k]
                        cols[col_k].discard(r2)
                        if col_k in active_cols and len(cols[col_k]) == 1:
                            col_deg1.append(col_k)
                else:
                    r2_map[col_k] = nv
                    bl = abs(nv).bit_length()
                    if bl > max_bits:
                        max_bits = bl
                    cols.setdefault(col_k, set()).add(r2)
            lr2 = len(r2_map)
            if lr2 == 0:
                if rhs[r2] != 0:
                    return r2
                active_rows.discard(r2)
                del rows[r2]
            elif lr2 == 1:
                row_deg1.append(r2)
            elif lr2 == 2:
                row_deg2.append(r2)

        other_entries = {k: v for k, v in piv_row.items() if k != j_piv}
        backsub_stack.append((j_piv, piv_val, other_entries, c_piv))
        for col_k in list(piv_row.keys()):
            cols[col_k].discard(r_piv)
            if col_k != j_piv and col_k in active_cols:
                d = len(cols[col_k])
                if d == 1:
                    col_deg1.append(col_k)
                elif d == 0:
                    active_cols.discard(col_k)
        del rows[r_piv]
        active_rows.discard(r_piv)
        active_cols.discard(j_piv)
        cols.pop(j_piv, None)
        peeled_rank += 1
        return None

    while True:
        progress = False
        while row_deg1 or col_deg1:
            while col_deg1:
                j = col_deg1.popleft()
                if j not in active_cols:
                    continue
                cset = cols.get(j)
                if not cset:
                    active_cols.discard(j)
                    continue
                if len(cset) != 1:
                    continue
                r = next(iter(cset))
                if r not in active_rows:
                    continue
                v = rows[r].get(j, 0)
                if v == 1 or v == -1:
                    other_entries = {k: val for k, val in rows[r].items() if k != j}
                    backsub_stack.append((j, v, other_entries, rhs[r]))
                    for col_k in list(rows[r].keys()):
                        cols[col_k].discard(r)
                        if col_k != j and col_k in active_cols:
                            d = len(cols[col_k])
                            if d == 1:
                                col_deg1.append(col_k)
                            elif d == 0:
                                active_cols.discard(col_k)
                    del rows[r]
                    active_rows.discard(r)
                    active_cols.discard(j)
                    cols.pop(j, None)
                    peeled_rank += 1
                    progress = True

            while row_deg1:
                r = row_deg1.popleft()
                if r not in active_rows:
                    continue
                rmap = rows.get(r)
                if not rmap:
                    if rhs[r] != 0:
                        return PeelingOutcome(True, r, peeled_rank, SparseIntMatrix(0, 0), [], [], [], backsub_stack, ops_log, max_bits)
                    active_rows.discard(r)
                    continue
                if len(rmap) != 1:
                    continue
                j, v = next(iter(rmap.items()))
                if v == 1 or v == -1:
                    contra_r = eliminate_unit_pivot(r, j)
                    progress = True
                    if contra_r is not None:
                        return PeelingOutcome(True, contra_r, peeled_rank, SparseIntMatrix(0, 0), [], [], [], backsub_stack, ops_log, max_bits)
                    break

        while row_deg2 and not row_deg1 and not col_deg1:
            r = row_deg2.popleft()
            if r not in active_rows:
                continue
            rmap = rows.get(r)
            if not rmap or len(rmap) != 2:
                continue
            items = list(rmap.items())
            (j1, v1), (j2, v2) = items[0], items[1]
            u1, u2 = (v1 == 1 or v1 == -1), (v2 == 1 or v2 == -1)
            if u1 and u2:
                cand_j, other_v = (j1, v2) if len(cols[j1]) <= len(cols[j2]) else (j2, v1)
            elif u1:
                cand_j, other_v = j1, v2
            elif u2:
                cand_j, other_v = j2, v1
            else:
                continue
            ob = abs(other_v).bit_length()
            if ob > 1:
                if ob > max_bits_chain:
                    continue
                if any(r2 != r and abs(rows[r2][cand_j]).bit_length() + ob > max_bits_chain for r2 in cols[cand_j]):
                    continue
            contra_r = eliminate_unit_pivot(r, cand_j)
            progress = True
            if contra_r is not None:
                return PeelingOutcome(True, contra_r, peeled_rank, SparseIntMatrix(0, 0), [], [], [], backsub_stack, ops_log, max_bits)
            if row_deg1 or col_deg1:
                break

        if progress:
            continue
        if not active_rows or not active_cols:
            break

        best_piv: Optional[Tuple[int, int]] = None
        best_score = max_markowitz + 1
        checked = 0
        for j in active_cols:
            cdeg = len(cols[j])
            if cdeg == 0 or cdeg - 1 > best_score:
                continue
            for r in cols[j]:
                v = rows[r][j]
                if v != 1 and v != -1:
                    continue
                rdeg = len(rows[r])
                score = (rdeg - 1) * (cdeg - 1)
                if score >= best_score:
                    continue
                bit_cap = max_bits_chain if score <= 1 else max_bits_fill
                rmax = max(abs(x).bit_length() for x in rows[r].values())
                if rmax > bit_cap:
                    continue
                if any(r2 != r and abs(rows[r2][j]).bit_length() + rmax > bit_cap for r2 in cols[j]):
                    continue
                best_score = score
                best_piv = (r, j)
                if best_score <= 1:
                    break
            if best_score <= 1:
                break
            if best_piv is not None:
                checked += 1
                if checked >= 64:
                    break

        if best_piv is not None:
            contra_r = eliminate_unit_pivot(best_piv[0], best_piv[1])
            progress = True
            if contra_r is not None:
                return PeelingOutcome(True, contra_r, peeled_rank, SparseIntMatrix(0, 0), [], [], [], backsub_stack, ops_log, max_bits)
        if not progress:
            break

    core_orig_rows = sorted(active_rows)
    core_orig_cols = sorted(j for j in active_cols if cols.get(j))
    col_remap = {old_j: new_j for new_j, old_j in enumerate(core_orig_cols)}
    core_mat = SparseIntMatrix(len(core_orig_rows), len(core_orig_cols))
    core_rhs: List[int] = []
    for new_r, old_r in enumerate(core_orig_rows):
        core_rhs.append(rhs[old_r])
        for old_j, v in rows[old_r].items():
            core_mat.set_entry(new_r, col_remap[old_j], v)

    return PeelingOutcome(
        False, None, peeled_rank, core_mat, core_rhs, core_orig_rows, core_orig_cols, backsub_stack, ops_log, max_bits
    )


def _replay_ops_dual(ops_log: Sequence[Tuple[int, int, int]], seed_row: int, seed_coeff: int = 1) -> Dict[int, int]:
    w: Dict[int, int] = {seed_row: seed_coeff}
    for r2, r1, factor in reversed(ops_log):
        w2 = w.get(r2, 0)
        if w2 != 0:
            nv = w.get(r1, 0) - w2 * factor
            if nv == 0:
                w.pop(r1, None)
            else:
                w[r1] = nv
    return w


def _replay_ops_dual_map(
    ops_log: Sequence[Tuple[int, int, int]], w_init: Dict[int, int], modulus: Optional[int] = None
) -> Dict[int, int]:
    w: Dict[int, int] = dict(w_init)
    for r2, r1, factor in reversed(ops_log):
        w2 = w.get(r2, 0)
        if w2 != 0:
            nv = w.get(r1, 0) - w2 * factor
            if modulus is not None:
                nv %= modulus
            if nv == 0:
                w.pop(r1, None)
            else:
                w[r1] = nv
    return w


# ==============================================================================
# 61-Bit Modular Sparse Elimination, Multi-Prime CRT Determinant & Cramer Lifting
# ==============================================================================


def mod_prescreen_torsor(
    A: SparseIntMatrix,
    c: Sequence[int],
    prime: int,
    prefer_cols: Optional[Set[int]] = None,
    prefer_rows: Optional[Set[int]] = None,
    rng_tie: Optional[random.Random] = None,
) -> Tuple[int, bool, List[int], List[int]]:
    """Fast sparse Markowitz elimination over F_p for [A | c].

    Optional prefer_cols / prefer_rows steer pivot selection toward an independent
    second full-rank minor for Pernet-Stein / Storjohann Double-Determinant compression!
    """
    m, n = A.nrows, A.ncols
    rhs_col = n
    rows: Dict[int, Dict[int, int]] = {}
    cols: Dict[int, Set[int]] = {}
    active_rows: Set[int] = set()

    for r in range(m):
        rd: Dict[int, int] = {}
        arow = A.rows.get(r)
        if arow:
            for j, v in arow.items():
                vm = v % prime
                if vm:
                    rd[j] = vm
                    cols.setdefault(j, set()).add(r)
        cm = c[r] % prime
        if cm:
            rd[rhs_col] = cm
        if rd:
            rows[r] = rd
            active_rows.add(r)

    piv_rows: List[int] = []
    piv_cols: List[int] = []

    while active_rows:
        best_r = -1
        best_j = -1
        best_key = (2, 1 << 60, 0)
        checked = 0
        for r in active_rows:
            rd = rows[r]
            rdeg = len(rd) - (1 if rhs_col in rd else 0)
            if rdeg == 0:
                continue
            r_pen = 0 if (prefer_rows is None or r in prefer_rows) else 1
            for j in rd:
                if j == rhs_col:
                    continue
                c_pen = 0 if (prefer_cols is None or j in prefer_cols) else 1
                pen = r_pen + c_pen
                if pen > best_key[0]:
                    continue
                score = (rdeg - 1) * (len(cols[j]) - 1)
                tie = rng_tie.randrange(1 << 20) if rng_tie is not None else 0
                key = (pen, score, tie)
                if key < best_key:
                    best_key = key
                    best_r = r
                    best_j = j
                    if pen == 0 and score == 0:
                        break
            if best_key[0] == 0 and best_key[1] == 0:
                break
            if best_r != -1 and prefer_cols is None and prefer_rows is None:
                checked += 1
                if checked >= 64 and best_key[1] <= 4:
                    break

        if best_r == -1:
            break

        piv_rows.append(best_r)
        piv_cols.append(best_j)
        active_rows.remove(best_r)
        piv_row = rows[best_r]
        inv_piv = pow(piv_row[best_j], prime - 2, prime)

        for j in piv_row:
            if j != rhs_col:
                cols[j].discard(best_r)

        targets = list(cols.get(best_j, ()))
        for r2 in targets:
            if r2 not in active_rows:
                continue
            r2_map = rows[r2]
            factor = (r2_map[best_j] * inv_piv) % prime
            for col_k, pv in piv_row.items():
                nv = (r2_map.get(col_k, 0) - factor * pv) % prime
                if nv == 0:
                    if col_k in r2_map:
                        del r2_map[col_k]
                        if col_k != rhs_col:
                            cols[col_k].discard(r2)
                else:
                    r2_map[col_k] = nv
                    if col_k != rhs_col:
                        cols.setdefault(col_k, set()).add(r2)
            if not r2_map:
                active_rows.discard(r2)

    consistent = all(rhs_col not in rows[r] for r in active_rows)
    return len(piv_rows), consistent, piv_rows, piv_cols


def sparse_minor_det_and_solve_mod_p(
    A: SparseIntMatrix,
    piv_rows: Sequence[int],
    piv_cols: Sequence[int],
    prime: int,
    rhs_p: Optional[Sequence[int]] = None,
) -> Tuple[int, Optional[List[int]]]:
    """Compute exact signed det(A[P, J]) mod p AND optionally adj(A[P, J]) @ rhs_p mod p
    (= det * x mod p) via sparse Markowitz elimination over F_p.

    Exact permutation sign tracking ensures every prime sees the identical signed det!
    """
    r = len(piv_rows)
    if r == 0:
        return 1, ([] if rhs_p is not None else None)

    col_map = {orig_c: idx for idx, orig_c in enumerate(piv_cols)}
    rows: Dict[int, Dict[int, int]] = {}
    cols: Dict[int, Set[int]] = {}
    rhs_vec = [v % prime for v in rhs_p] if rhs_p is not None else None
    active_rows: Set[int] = set()

    for i, orig_r in enumerate(piv_rows):
        rd: Dict[int, int] = {}
        arow = A.rows.get(orig_r)
        if arow:
            for orig_c, v in arow.items():
                j = col_map.get(orig_c)
                if j is not None:
                    vm = v % prime
                    if vm:
                        rd[j] = vm
                        cols.setdefault(j, set()).add(i)
        if not rd:
            return 0, None
        rows[i] = rd
        active_rows.add(i)

    det_prod = 1
    row_order: List[int] = []
    col_order: List[int] = []
    piv_data: List[Tuple[int, int, Dict[int, int], int]] = []

    for _ in range(r):
        best_r = -1
        best_j = -1
        best_score = 1 << 60
        checked = 0
        for ri in active_rows:
            rd = rows[ri]
            rdeg = len(rd)
            if rdeg == 0:
                return 0, None
            for cj in rd:
                score = (rdeg - 1) * (len(cols[cj]) - 1)
                if score < best_score:
                    best_score = score
                    best_r = ri
                    best_j = cj
                    if score == 0:
                        break
            if best_score == 0:
                break
            if best_r != -1:
                checked += 1
                if checked >= 64 and best_score <= 4:
                    break

        if best_r == -1:
            return 0, None

        active_rows.remove(best_r)
        piv_row = rows[best_r]
        piv_val = piv_row[best_j]
        det_prod = (det_prod * piv_val) % prime
        inv_piv = pow(piv_val, prime - 2, prime)
        row_order.append(best_r)
        col_order.append(best_j)
        if rhs_vec is not None:
            piv_data.append((best_j, inv_piv, dict(piv_row), rhs_vec[best_r]))

        for cj in piv_row:
            cols[cj].discard(best_r)

        targets = list(cols.get(best_j, ()))
        for r2 in targets:
            if r2 not in active_rows:
                continue
            r2_map = rows[r2]
            factor = (r2_map[best_j] * inv_piv) % prime
            if rhs_vec is not None:
                rhs_vec[r2] = (rhs_vec[r2] - factor * rhs_vec[best_r]) % prime
            for col_k, pv in piv_row.items():
                nv = (r2_map.get(col_k, 0) - factor * pv) % prime
                if nv == 0:
                    if col_k in r2_map:
                        del r2_map[col_k]
                        cols[col_k].discard(r2)
                else:
                    r2_map[col_k] = nv
                    cols.setdefault(col_k, set()).add(r2)

    sign = _perm_sign(row_order) * _perm_sign(col_order)
    det_signed = (det_prod if sign > 0 else (-det_prod)) % prime

    if rhs_vec is None:
        return det_signed, None

    # Exact back-substitution mod p for x = A[P,J]^{-1} rhs_p mod p, then scale by det_signed!
    x_mod = [0] * r
    for cj, inv_piv, piv_row, b_val in reversed(piv_data):
        acc = b_val
        for col_k, pv in piv_row.items():
            if col_k != cj:
                acc = (acc - pv * x_mod[col_k]) % prime
        x_mod[cj] = (acc * inv_piv) % prime

    adj_rhs_mod = [(det_signed * xv) % prime for xv in x_mod]
    return det_signed, adj_rhs_mod


def _hadamard_minor_bound(
    A: SparseIntMatrix,
    piv_rows: Sequence[int],
    piv_cols: Sequence[int],
    rhs_p: Optional[Sequence[int]] = None,
) -> int:
    """Exact integer Hadamard upper bound >= |det(A[P, J])| (and Cramer numerators if rhs_p given)."""
    col_set = set(piv_cols)
    bound = 1
    max_rhs_norm = 1
    if rhs_p is not None:
        sq_rhs = sum(v * v for v in rhs_p)
        max_rhs_norm = max(1, math.isqrt(sq_rhs) + 1)
    for orig_r in piv_rows:
        arow = A.rows.get(orig_r)
        sq = 0
        if arow:
            for c, v in arow.items():
                if c in col_set:
                    sq += v * v
        bound *= max(1, math.isqrt(sq) + 1)
    return bound * max_rhs_norm


def _crt_combine(residues: Sequence[int], primes: Sequence[int]) -> int:
    """Combine signed residues via exact incremental CRT and center into (-M/2, M/2]."""
    val = residues[0] % primes[0]
    mod = primes[0]
    for rk, pk in zip(residues[1:], primes[1:]):
        t = ((rk - val) * pow(mod, -1, pk)) % pk
        val += mod * t
        mod *= pk
    if val > (mod >> 1):
        val -= mod
    return val


def sparse_minor_crt_det_and_adj_solve(
    A: SparseIntMatrix,
    piv_rows: Sequence[int],
    piv_cols: Sequence[int],
    rhs_p: Optional[Sequence[int]] = None,
) -> Tuple[int, Optional[List[int]], int]:
    """Exact Hadamard-bounded 61-bit Multi-Prime CRT determinant & adjugate linear solver.

    Returns (det_abs, adj_x_int, max_bits) where:
      - det_abs == |det(A[P, J])| (100% exact!)
      - If rhs_p is provided and det_abs > 0: A[P, J] @ adj_x_int == det_abs * rhs_p (exact integers!)
    """
    r = len(piv_rows)
    if r == 0:
        return 1, ([] if rhs_p is not None else None), 0

    h_bound = _hadamard_minor_bound(A, piv_rows, piv_cols, rhs_p=rhs_p)
    target = 2 * h_bound + 1
    # Estimate number of 61-bit primes needed
    n_primes = max(1, (target.bit_length() + 59) // 60)
    primes = _get_crt_primes(n_primes)
    prod = 1
    for p in primes:
        prod *= p
    while prod <= target:
        n_primes += 1
        primes = _get_crt_primes(n_primes)
        prod *= primes[-1]

    det_res: List[int] = []
    vec_res: List[List[int]] = [[] for _ in range(r)] if rhs_p is not None else []
    for p in primes:
        dp, vp = sparse_minor_det_and_solve_mod_p(A, piv_rows, piv_cols, p, rhs_p=rhs_p)
        det_res.append(dp)
        if rhs_p is not None:
            if vp is None:
                # Could happen if prime p divides det! Re-solve with fresh prime not dividing det!
                # Wait: handle prime-divides-det cleanly by swapping in an extra prime!
                extra_idx = len(primes)
                while vp is None:
                    extra_idx += 1
                    p_new = _get_crt_primes(extra_idx)[-1]
                    dp, vp = sparse_minor_det_and_solve_mod_p(A, piv_rows, piv_cols, p_new, rhs_p=rhs_p)
                    if dp == 0 and extra_idx > len(primes) + 5:
                        return 0, None, 61
                    if vp is not None:
                        primes = list(primes)
                        primes[len(det_res) - 1] = p_new
                        det_res[-1] = dp
            for i in range(r):
                vec_res[i].append(vp[i])

    det_signed = _crt_combine(det_res, primes)
    if det_signed == 0:
        return 0, None, 61
    det_abs = abs(det_signed)
    max_bits = max(61, det_abs.bit_length())

    if rhs_p is None:
        return det_abs, None, max_bits

    sign = 1 if det_signed > 0 else -1
    adj_x = [sign * _crt_combine(vec_res[i], primes) for i in range(r)]
    for v in adj_x:
        bl = abs(v).bit_length()
        if bl > max_bits:
            max_bits = bl
    return det_abs, adj_x, max_bits


def _build_sparse_random_combination(
    A_sub: SparseIntMatrix,
    base_cols: Sequence[int],
    extra_cols: Sequence[int],
    seed: int,
) -> Tuple[SparseIntMatrix, List[List[Tuple[int, int]]]]:
    """Build sparse square r x r matrix M = A_sub @ R where each column k of R
    combines base_cols[k] with 1-2 extra columns using small {-2,-1,1,2} integer weights:
        M[:, k] = A_sub[:, base_cols[k]] + w1 * A_sub[:, extra1] (+ w2 * A_sub[:, extra2])
    Returns (M, R_cols) where R_cols[k] = [(orig_col, weight), ...].
    Guarantee: M * Z^r <= A_sub * Z^n and prod(invariant_factors(A_sub)) | det(M)!
    """
    r = len(base_cols)
    rng = random.Random(seed)
    n_ext = len(extra_cols)
    M = SparseIntMatrix(A_sub.nrows, r)
    R_cols: List[List[Tuple[int, int]]] = []

    # Pre-index columns of A_sub for O(nnz) construction
    col_entries: Dict[int, List[Tuple[int, int]]] = {}
    for row_i, rmap in A_sub.rows.items():
        for col_j, val in rmap.items():
            col_entries.setdefault(col_j, []).append((row_i, val))

    weights = (-1, 1)
    for k in range(r):
        e1 = extra_cols[(k + rng.randrange(n_ext)) % n_ext]
        w1 = weights[(k + rng.randrange(2)) & 1]
        terms: List[Tuple[int, int]] = [(base_cols[k], 1), (e1, w1)]
        R_cols.append(terms)
        acc: Dict[int, int] = {}
        for c_orig, wt in terms:
            for row_i, v in col_entries.get(c_orig, ()):
                nv = acc.get(row_i, 0) + wt * v
                if nv == 0:
                    acc.pop(row_i, None)
                else:
                    acc[row_i] = nv
        for row_i, val in acc.items():
            M.set_entry(row_i, k, val)
    return M, R_cols


def double_det_lattice_bound(
    A: SparseIntMatrix,
    P1: Sequence[int],
    J1: Sequence[int],
    allow_row_variation: bool = False,
    D1_known: Optional[int] = None,
) -> Tuple[int, int, List[Tuple[SparseIntMatrix, List[int], List[List[Tuple[int, int]]], int]], int]:
    """Pernet-Stein / Storjohann Randomized Double-Determinant Compression: G = gcd(D_1, D_2[, D_3]).

    Uses sparse randomized integer column combinations M_k = A_P @ R_k (2-3 terms per col)
    to break shared smooth/tree-edge factors that overlap in pure column subsets J_1, J_2!

    Returns (G, D1, completions_list, max_bits) where each entry in completions_list is:
        (M_mat, row_indices_of_M, R_cols_map_to_A, D_k)
    Guarantee:
      - If allow_row_variation is False (Torsor on A_P): G * Z^r <= A_P * Z^n!
      - If allow_row_variation is True (SNF on B): prod(invariant_factors(B)) | G!
    """
    r = len(P1)
    if r == 0:
        return 1, 1, [], 0
    if D1_known is not None:
        D1 = D1_known
        max_bits = D1.bit_length()
    else:
        D1, _, max_bits = sparse_minor_crt_det_and_adj_solve(A, P1, J1)
    if D1 == 0:
        return 0, 0, [], max_bits

    # First completion is the identity minor M_1 = A[P1, J1]
    A_P = A.row_subset(P1)
    M1 = SparseIntMatrix(r, r)
    j1_map = {oj: idx for idx, oj in enumerate(J1)}
    for i in range(r):
        for oj, v in A_P.rows.get(i, {}).items():
            idx = j1_map.get(oj)
            if idx is not None:
                M1.set_entry(i, idx, v)
    R1_cols: List[List[Tuple[int, int]]] = [[(oj, 1)] for oj in J1]
    id_rows = list(range(r))
    completions: List[Tuple[SparseIntMatrix, List[int], List[List[Tuple[int, int]]], int]] = [
        (M1, id_rows, R1_cols, D1)
    ]
    G = D1
    if G == 1:
        return 1, D1, completions, max_bits

    extra_cols = [j for j in range(A.ncols) if j not in j1_map]
    # Also handle tall matrices (p > r, n == r) via transpose randomized row combinations for SNF!
    if not extra_cols and allow_row_variation and A.nrows > r:
        AT = A.transpose()
        G_t, _, _, tb = double_det_lattice_bound(AT, J1, P1, allow_row_variation=False, D1_known=D1)
        return G_t, D1, completions, max(max_bits, tb)

    if not extra_cols:
        return G, D1, completions, max_bits

    # Generate up to 2 sparse randomized column completions M_k = A_P @ R_k!
    for attempt in range(2):
        M_k, R_k = _build_sparse_random_combination(A_P, J1, extra_cols, seed=20261119 + 97 * attempt)
        # Quick 61-bit mod check to ensure M_k is nonsingular before full CRT!
        d_chk, _ = sparse_minor_det_and_solve_mod_p(M_k, id_rows, id_rows, PRIME_1)
        if d_chk == 0:
            continue
        Dk, _, b_bits = sparse_minor_crt_det_and_adj_solve(M_k, id_rows, id_rows)
        if b_bits > max_bits:
            max_bits = b_bits
        if Dk > 0:
            G_new = math.gcd(G, Dk)
            if G_new < G or len(completions) < 2:
                completions.append((M_k, id_rows, R_k, Dk))
                G = G_new
            if G == 1 or (G.bit_length() <= 16 and attempt == 0):
                break

    # If allow_row_variation and extra rows exist (p > r) and G still has spurious row-minor factors,
    # also fold one sparse randomized row combination on A^T!
    if allow_row_variation and A.nrows > r and G > 1:
        extra_rows = [i for i in range(A.nrows) if i not in set(P1)]
        if extra_rows:
            AT = A.transpose()
            AT_J = AT.row_subset(J1)
            M_r, _ = _build_sparse_random_combination(AT_J, P1, extra_rows, seed=20261119 + 555)
            d_chk, _ = sparse_minor_det_and_solve_mod_p(M_r, id_rows, id_rows, PRIME_1)
            if d_chk != 0:
                Dr, _, rb = sparse_minor_crt_det_and_adj_solve(M_r, id_rows, id_rows)
                if rb > max_bits:
                    max_bits = rb
                if Dr > 0:
                    G = math.gcd(G, Dr)

    return G, D1, completions, max_bits


# ==============================================================================
# Sparse q-adic Local Torsion Checker & Prime-Power Digit-SNF (Cycle 5 Core!)
# ==============================================================================


def _val_q(x: int, q: int) -> int:
    v = 0
    while x % q == 0:
        x //= q
        v += 1
    return v


def _solve_torsor_mod_prime_power(
    A_P: SparseIntMatrix,
    c_P: Sequence[int],
    q: int,
    exp_e: int,
    want_solution: bool = True,
) -> Tuple[bool, Optional[List[int]], Optional[Tuple[Dict[int, int], int]]]:
    """Exact sparse q-adic solver for A_P x == c_P (mod q^e) with dual torsion witness replay!

    Returns:
      - If solvable mod q^e: (True, x_mod_qe, None)
      - If unsolvable mod q^e: (False, None, (y_dict, q^k)) where y^T A_P == 0 (mod q^k)
        and y^T c_P != 0 (mod q^k)!
    """
    M = q ** exp_e
    m, n = A_P.nrows, A_P.ncols
    rows: Dict[int, Dict[int, int]] = {}
    cols: Dict[int, Set[int]] = {}
    rhs: List[int] = [v % M for v in c_P]
    active_rows: Set[int] = set()

    for r in range(m):
        rd: Dict[int, int] = {}
        arow = A_P.rows.get(r)
        if arow:
            for j, v in arow.items():
                vm = v % M
                if vm:
                    rd[j] = vm
                    cols.setdefault(j, set()).add(r)
        if not rd:
            if rhs[r] % M != 0:
                # Find minimal power q^k dividing all entries (= M) that fails to divide rhs[r]
                return False, None, ({r: 1}, M)
        else:
            rows[r] = rd
            active_rows.add(r)

    ops_log: List[Tuple[int, int, int]] = []
    # Back-substitution stack: (piv_col, level, q_pow, inv_u, other_row_entries, rhs_val)
    piv_stack: List[Tuple[int, int, int, int, Dict[int, int], int]] = []

    for level in range(exp_e):
        q_pow = q ** level
        mod_step = q ** (exp_e - level)
        while active_rows:
            best_r = -1
            best_j = -1
            best_score = 1 << 60
            checked = 0
            for r in active_rows:
                rd = rows[r]
                rdeg = len(rd)
                for j, val in rd.items():
                    if (val // q_pow) % q != 0:
                        score = (rdeg - 1) * (len(cols[j]) - 1)
                        if score < best_score:
                            best_score = score
                            best_r = r
                            best_j = j
                            if score == 0:
                                break
                if best_score == 0:
                    break
                if best_r != -1:
                    checked += 1
                    if checked >= 64 and best_score <= 4:
                        break
            if best_r == -1:
                break

            active_rows.remove(best_r)
            piv_row = rows[best_r]
            piv_val = piv_row[best_j]
            # Check divisibility of rhs[best_r] by q_pow!
            if rhs[best_r] % q_pow != 0:
                # Row best_r has ALL matrix entries divisible by q_pow, yet rhs not divisible!
                y_w = _replay_ops_dual_map(ops_log, {best_r: 1}, modulus=q_pow)
                return False, None, (y_w, q_pow)

            u_unit = (piv_val // q_pow) % mod_step
            inv_u = pow(u_unit, -1, mod_step)

            for j in piv_row:
                cols[j].discard(best_r)

            targets = list(cols.get(best_j, ()))
            for r2 in targets:
                if r2 not in active_rows:
                    continue
                r2_map = rows[r2]
                v2 = r2_map[best_j]
                factor = ((v2 // q_pow) * inv_u) % mod_step
                ops_log.append((r2, best_r, factor))
                rhs[r2] = (rhs[r2] - factor * rhs[best_r]) % M
                for col_k, pv in piv_row.items():
                    nv = (r2_map.get(col_k, 0) - factor * pv) % M
                    if nv == 0:
                        if col_k in r2_map:
                            del r2_map[col_k]
                            cols[col_k].discard(r2)
                    else:
                        r2_map[col_k] = nv
                        cols.setdefault(col_k, set()).add(r2)
                if not r2_map:
                    active_rows.discard(r2)
                    if rhs[r2] % M != 0:
                        y_w = _replay_ops_dual_map(ops_log, {r2: 1}, modulus=M)
                        return False, None, (y_w, M)

            if want_solution:
                other = {k: v for k, v in piv_row.items() if k != best_j}
                piv_stack.append((best_j, level, q_pow, inv_u, other, rhs[best_r]))

        # After exhausting `level`, every remaining active row has all entries divisible by q^(level+1)!
        next_q_pow = q ** (level + 1)
        for r in list(active_rows):
            if rhs[r] % next_q_pow != 0:
                y_w = _replay_ops_dual_map(ops_log, {r: 1}, modulus=next_q_pow)
                return False, None, (y_w, next_q_pow)

    for r in active_rows:
        if rhs[r] % M != 0:
            y_w = _replay_ops_dual_map(ops_log, {r: 1}, modulus=M)
            return False, None, (y_w, M)

    if not want_solution:
        return True, None, None

    # Exact back-substitution mod q^e (free variables = 0)
    x_mod = [0] * n
    for piv_j, level, q_pow, inv_u, other, b_val in reversed(piv_stack):
        mod_step = q ** (exp_e - level)
        acc = b_val
        for col_k, pv in other.items():
            if x_mod[col_k]:
                acc = (acc - pv * x_mod[col_k]) % M
        # acc is guaranteed divisible by q_pow
        x_mod[piv_j] = ((acc // q_pow) * inv_u) % mod_step
    return True, x_mod, None


def _snf_prime_power_sparse(B: SparseIntMatrix, rank_r: int, q: int, exp_e: int) -> List[int]:
    """Prime-Power Local Sparse Digit-SNF (arXiv:2511.00677 / Storjohann).

    Computes exact q-adic invariant factors q^{v_1} | q^{v_2} | ... | q^{v_r} over Z / q^{e+1} Z
    using O(nnz) sparse Markowitz elimination of unit pivots!
    """
    M = q ** (exp_e + 1)
    rows: Dict[int, Dict[int, int]] = {}
    cols: Dict[int, Set[int]] = {}
    active_rows: Set[int] = set()

    for r, arow in B.rows.items():
        rd: Dict[int, int] = {}
        for j, v in arow.items():
            vm = v % M
            if vm:
                rd[j] = vm
                cols.setdefault(j, set()).add(r)
        if rd:
            rows[r] = rd
            active_rows.add(r)

    exponents: List[int] = []
    for level in range(exp_e + 1):
        if len(exponents) == rank_r or not active_rows:
            break
        q_pow = q ** level
        mod_step = q ** (exp_e + 1 - level)
        while active_rows and len(exponents) < rank_r:
            best_r = -1
            best_j = -1
            best_score = 1 << 60
            checked = 0
            for r in active_rows:
                rd = rows[r]
                rdeg = len(rd)
                for j, val in rd.items():
                    if (val // q_pow) % q != 0:
                        score = (rdeg - 1) * (len(cols[j]) - 1)
                        if score < best_score:
                            best_score = score
                            best_r = r
                            best_j = j
                            if score == 0:
                                break
                if best_score == 0:
                    break
                if best_r != -1:
                    checked += 1
                    if checked >= 64 and best_score <= 4:
                        break
            if best_r == -1:
                break

            active_rows.remove(best_r)
            piv_row = rows[best_r]
            u_unit = (piv_row[best_j] // q_pow) % mod_step
            inv_u = pow(u_unit, -1, mod_step)
            exponents.append(level)

            for j in piv_row:
                cols[j].discard(best_r)

            targets = list(cols.get(best_j, ()))
            for r2 in targets:
                if r2 not in active_rows:
                    continue
                r2_map = rows[r2]
                factor = ((r2_map[best_j] // q_pow) * inv_u) % mod_step
                for col_k, pv in piv_row.items():
                    nv = (r2_map.get(col_k, 0) - factor * pv) % M
                    if nv == 0:
                        if col_k in r2_map:
                            del r2_map[col_k]
                            cols[col_k].discard(r2)
                    else:
                        r2_map[col_k] = nv
                        cols.setdefault(col_k, set()).add(r2)
                if not r2_map:
                    active_rows.discard(r2)

    assert len(exponents) == rank_r, f"Digit-SNF rank mismatch at q={q}: {len(exponents)} != {rank_r}"
    exponents.sort()
    return [q ** v for v in exponents]


# ==============================================================================
# Guardrail A Phase 1 (Markowitz Q) + Bareiss + Mod-D Column HNF + Double-Det Fast Path
# ==============================================================================


def markowitz_q_phase1(
    A: SparseIntMatrix,
    c: Sequence[int],
    want_dual_witness: bool = True,
) -> Tuple[bool, List[int], List[int], Optional[Dict[int, int]], int]:
    """Exact sparse primitive Markowitz row reduction over Q on [A | c]."""
    m, n = A.nrows, A.ncols
    rhs_col = n
    rows: Dict[int, Dict[int, int]] = {}
    cols: Dict[int, Set[int]] = {}
    active_rows: Set[int] = set()
    row_combs: Optional[Dict[int, Dict[int, int]]] = {} if want_dual_witness else None
    max_bits = max(A.max_bit_length(), max((abs(v).bit_length() for v in c), default=0))

    for r in range(m):
        rd: Dict[int, int] = {}
        arow = A.rows.get(r)
        if arow:
            for j, v in arow.items():
                if v != 0:
                    rd[j] = v
                    cols.setdefault(j, set()).add(r)
        if c[r] != 0:
            rd[rhs_col] = c[r]
        if rd:
            rows[r] = rd
            active_rows.add(r)
            if row_combs is not None:
                row_combs[r] = {r: 1}

    piv_rows: List[int] = []
    piv_cols: List[int] = []

    while active_rows:
        best_r = -1
        best_j = -1
        best_key = (1 << 60, 1 << 60)
        checked = 0
        for r in active_rows:
            rd = rows[r]
            rdeg = len(rd) - (1 if rhs_col in rd else 0)
            if rdeg == 0:
                continue
            for j, val in rd.items():
                if j == rhs_col:
                    continue
                score = (rdeg - 1) * (len(cols[j]) - 1)
                key = (score, abs(val).bit_length())
                if key < best_key:
                    best_key = key
                    best_r = r
                    best_j = j
                    if key == (0, 1):
                        break
            if best_key == (0, 1):
                break
            if best_r != -1:
                checked += 1
                if checked >= 64 and best_key[0] <= 2:
                    break

        if best_r == -1:
            break

        piv_rows.append(best_r)
        piv_cols.append(best_j)
        active_rows.remove(best_r)
        piv_row = rows[best_r]
        piv_val = piv_row[best_j]
        piv_comb = row_combs[best_r] if row_combs is not None else None

        for j in piv_row:
            if j != rhs_col:
                cols[j].discard(best_r)

        targets = list(cols.get(best_j, ()))
        for r2 in targets:
            if r2 not in active_rows:
                continue
            r2_map = rows[r2]
            v = r2_map[best_j]
            g = math.gcd(abs(piv_val), abs(v))
            m_r2 = piv_val // g
            m_piv = v // g

            if m_r2 != 1:
                for col_k in list(r2_map.keys()):
                    if col_k not in piv_row:
                        r2_map[col_k] *= m_r2
            for col_k, pv in piv_row.items():
                nv = r2_map.get(col_k, 0) * m_r2 - m_piv * pv
                if nv == 0:
                    if col_k in r2_map:
                        del r2_map[col_k]
                        if col_k != rhs_col:
                            cols[col_k].discard(r2)
                else:
                    r2_map[col_k] = nv
                    if col_k != rhs_col:
                        cols.setdefault(col_k, set()).add(r2)

            if row_combs is not None and piv_comb is not None:
                c2 = row_combs[r2]
                if m_r2 != 1:
                    for rk in list(c2.keys()):
                        c2[rk] *= m_r2
                for rk, cv in piv_comb.items():
                    nv = c2.get(rk, 0) - m_piv * cv
                    if nv == 0:
                        c2.pop(rk, None)
                    else:
                        c2[rk] = nv

            if not r2_map:
                active_rows.discard(r2)
                continue

            row_g = _gcd_values(r2_map.values())
            if row_combs is not None:
                div_g = math.gcd(row_g, _gcd_values(row_combs[r2].values()))
                if div_g > 1:
                    for col_k in r2_map:
                        r2_map[col_k] //= div_g
                    for rk in row_combs[r2]:
                        row_combs[r2][rk] //= div_g
            else:
                if row_g > 1:
                    for col_k in r2_map:
                        r2_map[col_k] //= row_g

            for val in r2_map.values():
                bl = abs(val).bit_length()
                if bl > max_bits:
                    max_bits = bl

    for r in active_rows:
        if rhs_col in rows[r]:
            w: Optional[Dict[int, int]] = None
            if row_combs is not None:
                w = row_combs[r]
                wg = _gcd_values(w.values())
                if wg > 1:
                    w = {k: v // wg for k, v in w.items()}
            return False, piv_rows, piv_cols, w, max_bits

    return True, piv_rows, piv_cols, None, max_bits


def bareiss_jordan_solve(
    A: SparseIntMatrix,
    c: Sequence[int],
    piv_rows: Sequence[int],
    piv_cols: Sequence[int],
) -> Tuple[int, List[int], int, int]:
    """Exact fraction-free Bareiss-Jordan elimination on A[P, J] x = c[P]."""
    r = len(piv_rows)
    if r == 0:
        return 1, [], 1, 0

    col_map = {orig_c: idx for idx, orig_c in enumerate(piv_cols)}
    M: List[List[int]] = [[0] * (r + 1) for _ in range(r)]
    max_bits = 0
    for i, orig_r in enumerate(piv_rows):
        arow = A.rows.get(orig_r)
        if arow:
            for orig_c, v in arow.items():
                j = col_map.get(orig_c)
                if j is not None:
                    M[i][j] = v
                    bl = abs(v).bit_length()
                    if bl > max_bits:
                        max_bits = bl
        M[i][r] = c[orig_r]
        bl = abs(c[orig_r]).bit_length()
        if bl > max_bits:
            max_bits = bl

    prev_piv = 1
    for k in range(r):
        if M[k][k] == 0:
            swap_i = next((i for i in range(k + 1, r) if M[i][k] != 0), -1)
            if swap_i == -1:
                return 0, [], 1, max_bits
            M[k], M[swap_i] = M[swap_i], M[k]
        piv = M[k][k]
        row_k = M[k]
        for i in range(r):
            if i == k:
                continue
            mik = M[i][k]
            row_i = M[i]
            if i < k:
                row_i[i] = piv
            for j in range(k + 1, r + 1):
                val = (row_i[j] * piv - mik * row_k[j]) // prev_piv
                row_i[j] = val
                bl = abs(val).bit_length()
                if bl > max_bits:
                    max_bits = bl
            row_i[k] = 0
        prev_piv = piv

    det_val = M[r - 1][r - 1]
    det_abs = abs(det_val)
    if det_abs == 0:
        return 0, [], 1, max_bits

    if det_val < 0:
        num_x = [-M[i][r] for i in range(r)]
        den_x = -det_val
    else:
        num_x = [M[i][r] for i in range(r)]
        den_x = det_val
    g = math.gcd(den_x, _gcd_values(num_x))
    if g > 1:
        den_x //= g
        num_x = [v // g for v in num_x]
    return det_abs, num_x, den_x, max_bits


def bareiss_det_dense(mat: Sequence[Sequence[int]]) -> Tuple[int, int]:
    """Exact fraction-free Bareiss determinant on a square dense integer matrix."""
    r = len(mat)
    if r == 0:
        return 1, 0
    B = [list(row) for row in mat]
    max_bits = max((abs(v).bit_length() for row in B for v in row), default=0)
    prev_piv = 1
    sign = 1
    for k in range(r):
        if B[k][k] == 0:
            swap_i = next((i for i in range(k + 1, r) if B[i][k] != 0), -1)
            if swap_i == -1:
                return 0, max_bits
            B[k], B[swap_i] = B[swap_i], B[k]
            sign = -sign
        piv = B[k][k]
        row_k = B[k]
        for i in range(k + 1, r):
            row_i = B[i]
            bik = row_i[k]
            for j in range(k + 1, r):
                val = (row_i[j] * piv - bik * row_k[j]) // prev_piv
                row_i[j] = val
                bl = abs(val).bit_length()
                if bl > max_bits:
                    max_bits = bl
            row_i[k] = 0
        prev_piv = piv
    return sign * B[r - 1][r - 1], max_bits


def _merge_col_into_lower_hnf_mod_d(H: List[List[int]], col_vec: Sequence[int], D: int) -> Tuple[bool, int]:
    r = len(H)
    w = [v % D for v in col_vec]
    max_bits = D.bit_length()
    changed = False

    for i in range(r):
        b = w[i]
        if b == 0:
            continue
        a = H[i][i]
        if b % a == 0:
            q = b // a
            w[i] = 0
            for k in range(i + 1, r):
                w[k] = (w[k] - q * H[k][i]) % D
            continue
        changed = True
        g, s, t = xgcd(a, b)
        a_g, b_g = a // g, b // g
        H[i][i] = g
        w[i] = 0
        for k in range(i + 1, r):
            hki, wk = H[k][i], w[k]
            nh = (s * hki + t * wk) % D
            nw = (-b_g * hki + a_g * wk) % D
            H[k][i], w[k] = nh, nw
            for val in (s * hki, t * wk, nh, nw):
                bl = abs(val).bit_length()
                if bl > max_bits:
                    max_bits = bl

    if changed:
        for i in range(r):
            for k in range(i + 1, r):
                hkk = H[k][k]
                if H[k][i] >= hkk or H[k][i] < 0:
                    q = H[k][i] // hkk
                    for m in range(k, r):
                        H[m][i] = (H[m][i] - q * H[m][k]) % D
    return changed, max_bits


def _lower_hnf_forward_sub(H: List[List[int]], rhs: Sequence[int]) -> Tuple[bool, List[int], Optional[Tuple[int, int, int]]]:
    r = len(H)
    z = [0] * r
    for i in range(r):
        acc = rhs[i]
        row_i = H[i]
        for k in range(i):
            acc -= row_i[k] * z[k]
        hii = row_i[i]
        rem = acc % hii
        if rem != 0:
            return False, z, (i, hii, rem)
        z[i] = acc // hii
    return True, z, None


def _build_torsion_dual_witness(H: List[List[int]], fail_row: int) -> Tuple[List[int], int]:
    r = len(H)
    f = fail_row
    v_num = [0] * (f + 1)
    v_den = [1] * (f + 1)
    v_num[f] = 1
    v_den[f] = H[f][f]
    for k in range(f - 1, -1, -1):
        lcm_d = 1
        for m in range(k + 1, f + 1):
            if H[m][k] != 0 and v_num[m] != 0:
                lcm_d = math.lcm(lcm_d, v_den[m])
        s_num = 0
        for m in range(k + 1, f + 1):
            if H[m][k] != 0 and v_num[m] != 0:
                s_num += H[m][k] * v_num[m] * (lcm_d // v_den[m])
        if s_num == 0:
            v_num[k], v_den[k] = 0, 1
        else:
            num, den = -s_num, lcm_d * H[k][k]
            g = math.gcd(abs(num), den)
            v_num[k], v_den[k] = num // g, den // g

    M = 1
    for d in v_den:
        M = math.lcm(M, d)
    y = [0] * r
    for k in range(f + 1):
        y[k] = v_num[k] * (M // v_den[k])
    g = math.gcd(M, _gcd_values(y))
    if g > 1:
        M //= g
        y = [v // g for v in y]
    return y, M


def _reconstruct_integral_witness_core(
    A_P_cols: List[List[int]],
    selected_col_indices: List[int],
    c_P: Sequence[int],
) -> Optional[Dict[int, int]]:
    r = len(c_P)
    k = len(selected_col_indices)
    M = [[A_P_cols[j][i] for j in range(k)] for i in range(r)]
    U = [[1 if i == j else 0 for j in range(k)] for i in range(k)]

    for i in range(r):
        while True:
            nz = [j for j in range(i, k) if M[i][j] != 0]
            if not nz:
                return None
            if len(nz) == 1:
                p = nz[0]
                if p != i:
                    for ri in range(r):
                        M[ri][i], M[ri][p] = M[ri][p], M[ri][i]
                    for ui in range(k):
                        U[ui][i], U[ui][p] = U[ui][p], U[ui][i]
                if M[i][i] < 0:
                    for ri in range(r):
                        M[ri][i] = -M[ri][i]
                    for ui in range(k):
                        U[ui][i] = -U[ui][i]
                break
            p = min(nz, key=lambda j: abs(M[i][j]))
            if p != i:
                for ri in range(r):
                    M[ri][i], M[ri][p] = M[ri][p], M[ri][i]
                for ui in range(k):
                    U[ui][i], U[ui][p] = U[ui][p], U[ui][i]
            piv = M[i][i]
            if piv < 0:
                for ri in range(r):
                    M[ri][i] = -M[ri][i]
                for ui in range(k):
                    U[ui][i] = -U[ui][i]
                piv = -piv
            for j in range(i + 1, k):
                if M[i][j] != 0:
                    q = M[i][j] // piv
                    if q != 0:
                        for ri in range(r):
                            M[ri][j] -= q * M[ri][i]
                        for ui in range(k):
                            U[ui][j] -= q * U[ui][i]
        piv = M[i][i]
        for j in range(i):
            if M[i][j] != 0:
                q = M[i][j] // piv
                if q != 0:
                    for ri in range(r):
                        M[ri][j] -= q * M[ri][i]
                    for ui in range(k):
                        U[ui][j] -= q * U[ui][i]

    H_sub = [row[:r] for row in M]
    ok, z, _ = _lower_hnf_forward_sub(H_sub, c_P)
    if not ok:
        return None
    sol: Dict[int, int] = {}
    for idx_j, orig_col in enumerate(selected_col_indices):
        val = sum(U[idx_j][t] * z[t] for t in range(r))
        if val != 0:
            sol[orig_col] = val
    return sol


def _bezout_lift_integral_witness(
    n_c: int,
    d_rhs: Sequence[int],
    completions: Sequence[Tuple[SparseIntMatrix, List[int], List[List[Tuple[int, int]]], int]],
) -> Tuple[List[int], int]:
    """Given M_k = A_P @ R_k with |det(M_k)| = D_k and G = gcd(D_1, ..., D_s),
    reconstruct exact integer w in Z^{n_c} satisfying A_P @ w == G * d_rhs
    via 61-bit CRT Cramer solving + Bezout linear combination!
    """
    g_cur = completions[0][3]
    coeffs = [1]
    for idx in range(1, len(completions)):
        g_new, s, t = xgcd(g_cur, completions[idx][3])
        coeffs = [c * s for c in coeffs] + [t]
        g_cur = g_new

    w = [0] * n_c
    max_bits = 0
    for (M_k, id_rows, R_k, Dk), s_k in zip(completions, coeffs):
        if s_k == 0:
            continue
        det_k, u_k, mb = sparse_minor_crt_det_and_adj_solve(M_k, id_rows, id_rows, rhs_p=d_rhs)
        assert det_k == Dk and u_k is not None
        if mb > max_bits:
            max_bits = mb
        for k_idx, u_val in enumerate(u_k):
            if u_val == 0:
                continue
            su = s_k * u_val
            for col_orig, wt in R_k[k_idx]:
                w[col_orig] += su * wt
                bl = abs(w[col_orig]).bit_length()
                if bl > max_bits:
                    max_bits = bl
    return w, max_bits


def _backsub_peeled(
    ncols: int,
    core_orig_cols: Sequence[int],
    core_sol: Sequence[int],
    backsub_stack: Sequence[Tuple[int, int, Dict[int, int], int]],
    den: int = 1,
) -> List[int]:
    x = [0] * ncols
    for idx, orig_c in enumerate(core_orig_cols):
        x[orig_c] = core_sol[idx]
    for col_j, piv_sign, other_entries, c_r in reversed(backsub_stack):
        acc = c_r * den
        for k, v in other_entries.items():
            acc -= v * x[k]
        x[col_j] = piv_sign * acc
    return x


def solve_torsor(
    A: SparseIntMatrix,
    c: Sequence[int],
    ring: str = "Z",
    want_witness: bool = True,
    use_prescreen: bool = True,
    use_double_det: bool = True,
    crt_rank_threshold: int = 32,
) -> TorsorResult:
    """Exact cellular sheaf affine torsor solver v2.0 for A x = c over ring in {'Z', 'Q'}.

    Upgrades over v1.0:
    - On large unpeeled cores (r > crt_rank_threshold), replaces dense Bareiss with
      61-bit Multi-Prime CRT + Double-Determinant compression G = gcd(D_1, D_2)
      and sparse q-adic local torsion verification + Bezout integral lifting!
    - Retains exact Bareiss + Mod-D Column-HNF for small cores (r <= crt_rank_threshold).
    """
    if ring not in ("Z", "Q"):
        raise ValueError(f"ring must be 'Z' or 'Q', got {ring!r}")
    if len(c) != A.nrows:
        raise ValueError(f"RHS length {len(c)} != nrows {A.nrows}")

    peel = dhsw_peel_torsor(A, c, record_ops=want_witness)
    max_bits = peel.max_bits

    if peel.unsat_free:
        w = None
        if want_witness and peel.empty_contradiction_row is not None:
            w = _replay_ops_dual(peel.ops_log, peel.empty_contradiction_row)
            wg = _gcd_values(w.values())
            if wg > 1:
                w = {k: v // wg for k, v in w.items()}
        return TorsorResult(
            status="UNSAT_FREE_COHOMOLOGY",
            ring=ring,
            rank_q=peel.peeled_rank,
            peeled_rank=peel.peeled_rank,
            core_shape=(0, 0),
            max_bits=max_bits,
            dual_free_witness=w,
        )

    A_core = peel.core_matrix
    c_core = peel.core_rhs
    m_c, n_c = A_core.nrows, A_core.ncols

    if m_c == 0:
        x_int = _backsub_peeled(A.ncols, peel.core_orig_cols, [0] * n_c, peel.backsub_stack, den=1) if want_witness else None
        return TorsorResult(
            status="SAT_INTEGRAL" if ring == "Z" else "SAT_Q",
            ring=ring,
            rank_q=peel.peeled_rank,
            peeled_rank=peel.peeled_rank,
            core_shape=(0, n_c),
            max_bits=max_bits,
            x_int=x_int if ring == "Z" else None,
            x_q_num=x_int if ring == "Q" else None,
            x_q_den=1,
        )

    # Step 2: 61-bit double-prime modular pre-screen on compressed core
    prescreen_agreed = True
    if use_prescreen and A_core.max_bit_length() < 60:
        r1, ok1, P1_piv, J1_piv = mod_prescreen_torsor(A_core, c_core, PRIME_1)
        r2, ok2, _, _ = mod_prescreen_torsor(A_core, c_core, PRIME_2)
        prescreen_agreed = (r1 == r2 and ok1 == ok2)

        if prescreen_agreed and ok1:
            # Solve minor A_core[P1, J1] x = c[P1] via Bareiss (small r) or 61-bit CRT (large r)!
            if r1 <= crt_rank_threshold:
                det_abs, num_j, den_j, b_bits = bareiss_jordan_solve(A_core, c_core, P1_piv, J1_piv)
            else:
                c_p1 = [c_core[orig_r] for orig_r in P1_piv]
                det_abs, adj_x, b_bits = sparse_minor_crt_det_and_adj_solve(
                    A_core, P1_piv, J1_piv, rhs_p=c_p1
                )
                if det_abs > 0 and adj_x is not None:
                    g = math.gcd(det_abs, _gcd_values(adj_x))
                    den_j = det_abs // g
                    num_j = [v // g for v in adj_x]
                else:
                    num_j, den_j = [], 1

            if b_bits > max_bits:
                max_bits = b_bits
            if det_abs > 0:
                x_core_num = [0] * n_c
                for idx_col, v in zip(J1_piv, num_j):
                    x_core_num[idx_col] = v
                lhs = A_core.matvec(x_core_num)
                if all(lhs[i] == den_j * c_core[i] for i in range(m_c)):
                    if ring == "Q":
                        x_full = _backsub_peeled(A.ncols, peel.core_orig_cols, x_core_num, peel.backsub_stack, den=den_j) if want_witness else None
                        return TorsorResult(
                            status="SAT_Q",
                            ring="Q",
                            rank_q=peel.peeled_rank + r1,
                            peeled_rank=peel.peeled_rank,
                            core_shape=(m_c, n_c),
                            max_bits=max_bits,
                            x_q_num=x_full,
                            x_q_den=den_j,
                            pivot_rows_core=P1_piv,
                            pivot_cols_core=J1_piv,
                            prescreen_agreed=True,
                        )
                    if den_j == 1:
                        x_full = _backsub_peeled(A.ncols, peel.core_orig_cols, x_core_num, peel.backsub_stack, den=1) if want_witness else None
                        return TorsorResult(
                            status="SAT_INTEGRAL",
                            ring="Z",
                            rank_q=peel.peeled_rank + r1,
                            peeled_rank=peel.peeled_rank,
                            core_shape=(m_c, n_c),
                            max_bits=max_bits,
                            x_int=x_full,
                            pivot_rows_core=P1_piv,
                            pivot_cols_core=J1_piv,
                            prescreen_agreed=True,
                        )
                    if m_c == r1:
                        return _phase2_z_torsor(
                            A=A,
                            peel=peel,
                            A_core=A_core,
                            c_core=c_core,
                            P=P1_piv,
                            J=J1_piv,
                            det_abs=det_abs,
                            num_j=num_j,
                            den_j=den_j,
                            max_bits=max_bits,
                            want_witness=want_witness,
                            prescreen_agreed=True,
                            use_double_det=use_double_det,
                            crt_rank_threshold=crt_rank_threshold,
                        )

    # Step 3: Guardrail A Phase 1 — Exact Primitive Markowitz Q-Solver on core
    sat_q, P, J, dual_core, m_bits = markowitz_q_phase1(A_core, c_core, want_dual_witness=want_witness)
    if m_bits > max_bits:
        max_bits = m_bits
    r_core = len(P)

    if not sat_q:
        dual_full = None
        if want_witness and dual_core is not None:
            w_orig_core = {peel.core_orig_rows[cr]: val for cr, val in dual_core.items()}
            dual_full = _replay_ops_dual_map(peel.ops_log, w_orig_core)
            wg = _gcd_values(dual_full.values())
            if wg > 1:
                dual_full = {k: v // wg for k, v in dual_full.items()}
        return TorsorResult(
            status="UNSAT_FREE_COHOMOLOGY",
            ring=ring,
            rank_q=peel.peeled_rank + r_core,
            peeled_rank=peel.peeled_rank,
            core_shape=(m_c, n_c),
            max_bits=max_bits,
            dual_free_witness=dual_full,
            pivot_rows_core=P,
            pivot_cols_core=J,
            prescreen_agreed=prescreen_agreed,
        )

    if ring == "Q":
        x_full = None
        den_j = 1
        if want_witness:
            if r_core <= crt_rank_threshold:
                det_abs, num_j, den_j, b_bits = bareiss_jordan_solve(A_core, c_core, P, J)
            else:
                c_p = [c_core[orig_r] for orig_r in P]
                det_abs, adj_x, b_bits = sparse_minor_crt_det_and_adj_solve(A_core, P, J, rhs_p=c_p)
                assert det_abs > 0 and adj_x is not None
                g = math.gcd(det_abs, _gcd_values(adj_x))
                den_j = det_abs // g
                num_j = [v // g for v in adj_x]
            if b_bits > max_bits:
                max_bits = b_bits
            x_core_num = [0] * n_c
            for idx_col, v in zip(J, num_j):
                x_core_num[idx_col] = v
            x_full = _backsub_peeled(A.ncols, peel.core_orig_cols, x_core_num, peel.backsub_stack, den=den_j)
        return TorsorResult(
            status="SAT_Q",
            ring="Q",
            rank_q=peel.peeled_rank + r_core,
            peeled_rank=peel.peeled_rank,
            core_shape=(m_c, n_c),
            max_bits=max_bits,
            x_q_num=x_full,
            x_q_den=den_j,
            pivot_rows_core=P,
            pivot_cols_core=J,
            prescreen_agreed=prescreen_agreed,
        )

    # Guardrail B: 1-row GCD torsion shortcut over Z (SAT_Q already certified!)
    for r_idx in range(m_c):
        row_map = A_core.rows.get(r_idx)
        if row_map:
            g = _gcd_values(row_map.values())
            if g > 1 and c_core[r_idx] % g != 0:
                dual_t = None
                if want_witness:
                    y_full = _replay_ops_dual_map(peel.ops_log, {peel.core_orig_rows[r_idx]: 1})
                    dual_t = (y_full, g)
                return TorsorResult(
                    status="UNSAT_TORSION",
                    ring="Z",
                    rank_q=peel.peeled_rank + r_core,
                    peeled_rank=peel.peeled_rank,
                    core_shape=(m_c, n_c),
                    max_bits=max_bits,
                    torsion_cert=(g, c_core[r_idx] % g),
                    dual_torsion_witness=dual_t,
                    pivot_rows_core=P,
                    pivot_cols_core=J,
                    prescreen_agreed=prescreen_agreed,
                )

    if r_core <= crt_rank_threshold:
        det_abs, num_j, den_j, b_bits = bareiss_jordan_solve(A_core, c_core, P, J)
    else:
        c_p = [c_core[orig_r] for orig_r in P]
        det_abs, adj_x, b_bits = sparse_minor_crt_det_and_adj_solve(A_core, P, J, rhs_p=c_p)
        assert det_abs > 0 and adj_x is not None
        g = math.gcd(det_abs, _gcd_values(adj_x))
        den_j = det_abs // g
        num_j = [v // g for v in adj_x]
    if b_bits > max_bits:
        max_bits = b_bits

    return _phase2_z_torsor(
        A=A,
        peel=peel,
        A_core=A_core,
        c_core=c_core,
        P=P,
        J=J,
        det_abs=det_abs,
        num_j=num_j,
        den_j=den_j,
        max_bits=max_bits,
        want_witness=want_witness,
        prescreen_agreed=prescreen_agreed,
        use_double_det=use_double_det,
        crt_rank_threshold=crt_rank_threshold,
    )


def _phase2_z_torsor(
    A: SparseIntMatrix,
    peel: PeelingOutcome,
    A_core: SparseIntMatrix,
    c_core: Sequence[int],
    P: List[int],
    J: List[int],
    det_abs: int,
    num_j: List[int],
    den_j: int,
    max_bits: int,
    want_witness: bool,
    prescreen_agreed: bool,
    use_double_det: bool = True,
    crt_rank_threshold: int = 32,
) -> TorsorResult:
    """Guardrail A Phase 2 v2.0: Exact Z-lattice solvability of A_P x = c_P.

    - Uses Double-Determinant G = gcd(D_1, D_2) + sparse q-adic local check + Bezout witness lifting
      on large/unpeelable cores (r > crt_rank_threshold or D_1 > 2^40)!
    - Uses exact Mod-G Lower-Triangular Column-HNF on small cores (with tight G <= D_1!).
    """
    m_c, n_c = A_core.nrows, A_core.ncols
    r = len(P)
    d1_bits = det_abs.bit_length()

    if det_abs == 1 or den_j == 1:
        x_full = None
        if want_witness:
            x_core = [0] * n_c
            for col_idx, val in zip(J, num_j):
                x_core[col_idx] = val
            x_full = _backsub_peeled(A.ncols, peel.core_orig_cols, x_core, peel.backsub_stack, den=1)
        return TorsorResult(
            status="SAT_INTEGRAL",
            ring="Z",
            rank_q=peel.peeled_rank + r,
            peeled_rank=peel.peeled_rank,
            core_shape=(m_c, n_c),
            max_bits=max_bits,
            x_int=x_full,
            pivot_rows_core=P,
            pivot_cols_core=J,
            prescreen_agreed=prescreen_agreed,
            double_det_G=1,
            single_det_D1_bits=d1_bits,
        )

    c_P = [c_core[orig_r] for orig_r in P]

    # Cycle 5 Double-Determinant Compression G = gcd(D_1, D_2) when extra columns exist!
    G = det_abs
    completions: Optional[List[Tuple[SparseIntMatrix, List[int], List[List[Tuple[int, int]]], int]]] = None
    if use_double_det and n_c > r and (r > crt_rank_threshold or det_abs > 16):
        G, _, completions, dd_bits = double_det_lattice_bound(
            A_core, P, J, allow_row_variation=False, D1_known=det_abs
        )
        if dd_bits > max_bits:
            max_bits = dd_bits

    # Instant G == 1 unimodular certificate via Bezout lifting!
    if G == 1 and completions is not None:
        x_full = None
        if want_witness:
            x_core, lb = _bezout_lift_integral_witness(n_c, c_P, completions)
            if lb > max_bits:
                max_bits = lb
            x_full = _backsub_peeled(A.ncols, peel.core_orig_cols, x_core, peel.backsub_stack, den=1)
        return TorsorResult(
            status="SAT_INTEGRAL",
            ring="Z",
            rank_q=peel.peeled_rank + r,
            peeled_rank=peel.peeled_rank,
            core_shape=(m_c, n_c),
            max_bits=max_bits,
            x_int=x_full,
            pivot_rows_core=P,
            pivot_cols_core=J,
            prescreen_agreed=prescreen_agreed,
            double_det_G=1,
            single_det_D1_bits=d1_bits,
        )

    # Sparse Prime-Power Local Fast Path for large unpeeled cores (r > crt_rank_threshold)
    if r > crt_rank_threshold and use_double_det and completions is not None:
        pp = factor_prime_powers(G)
        if pp is not None:
            A_P_mat = A_core.row_subset(P)
            local_sols: List[Tuple[List[int], int]] = []
            for q, exp_e in pp:
                ok_q, x_mod_q, fail_dual = _solve_torsor_mod_prime_power(
                    A_P_mat, c_P, q, exp_e, want_solution=want_witness
                )
                if not ok_q:
                    assert fail_dual is not None
                    y_p_dict, mod_m = fail_dual
                    dual_t = None
                    if want_witness:
                        w_orig_core = {peel.core_orig_rows[P[i]]: val for i, val in y_p_dict.items() if val != 0}
                        y_full = _replay_ops_dual_map(peel.ops_log, w_orig_core)
                        dual_t = (y_full, mod_m)
                    yc_rem = sum(val * c_P[i] for i, val in y_p_dict.items()) % mod_m
                    return TorsorResult(
                        status="UNSAT_TORSION",
                        ring="Z",
                        rank_q=peel.peeled_rank + r,
                        peeled_rank=peel.peeled_rank,
                        core_shape=(m_c, n_c),
                        max_bits=max_bits,
                        torsion_cert=(mod_m, yc_rem),
                        dual_torsion_witness=dual_t,
                        pivot_rows_core=P,
                        pivot_cols_core=J,
                        prescreen_agreed=prescreen_agreed,
                        double_det_G=G,
                        single_det_D1_bits=d1_bits,
                    )
                if want_witness and x_mod_q is not None:
                    local_sols.append((x_mod_q, q ** exp_e))

            # Solvable modulo every prime power q^e || G ==> 100% CERTIFIED SAT_INTEGRAL!
            x_full = None
            if want_witness:
                x0 = [0] * n_c
                mods = [m_i for _, m_i in local_sols]
                for col_j in range(n_c):
                    res_j = [sol[col_j] for sol, _ in local_sols]
                    x0[col_j] = _crt_combine(res_j, mods) % G
                ax0 = A_P_mat.matvec(x0)
                d_prime = [(c_P[i] - ax0[i]) // G for i in range(r)]
                w_lift, lb = _bezout_lift_integral_witness(n_c, d_prime, completions)
                if lb > max_bits:
                    max_bits = lb
                x_core = [x0[j] + w_lift[j] for j in range(n_c)]
                x_full = _backsub_peeled(A.ncols, peel.core_orig_cols, x_core, peel.backsub_stack, den=1)

            return TorsorResult(
                status="SAT_INTEGRAL",
                ring="Z",
                rank_q=peel.peeled_rank + r,
                peeled_rank=peel.peeled_rank,
                core_shape=(m_c, n_c),
                max_bits=max_bits,
                x_int=x_full,
                pivot_rows_core=P,
                pivot_cols_core=J,
                prescreen_agreed=prescreen_agreed,
                double_det_G=G,
                single_det_D1_bits=d1_bits,
            )

    # Guardrail A Exact Modulo-G Lower-Triangular Column-HNF on A_P (tight modulus G <= D_1!)
    D = G
    col_vecs: Dict[int, List[int]] = {}
    for i, orig_r in enumerate(P):
        arow = A_core.rows.get(orig_r)
        if arow:
            for j, v in arow.items():
                vec = col_vecs.get(j)
                if vec is None:
                    vec = [0] * r
                    col_vecs[j] = vec
                vec[i] = v

    H = [[D if i == k else 0 for k in range(r)] for i in range(r)]
    generating_cols: List[int] = []
    seen_gen: Set[int] = set()
    seed_cols: List[int] = list(J)
    if completions is not None:
        for _, _, R_k, _ in completions:
            for col_terms in R_k:
                for orig_j, _ in col_terms:
                    seed_cols.append(orig_j)
    for j in seed_cols:
        if j not in seen_gen:
            seen_gen.add(j)
            generating_cols.append(j)
            _, mb = _merge_col_into_lower_hnf_mod_d(H, col_vecs.get(j, [0] * r), D)
            if mb > max_bits:
                max_bits = mb

    for j in sorted(col_vecs.keys()):
        if j in seen_gen:
            continue
        changed, mb = _merge_col_into_lower_hnf_mod_d(H, col_vecs[j], D)
        if mb > max_bits:
            max_bits = mb
        if changed:
            generating_cols.append(j)
            seen_gen.add(j)
            if all(H[i][i] == 1 for i in range(r)):
                break

    ok, _, fail_info = _lower_hnf_forward_sub(H, c_P)
    if not ok:
        assert fail_info is not None
        fail_row, h_ii, rem = fail_info
        dual_t = None
        if want_witness:
            y_p, mod_m = _build_torsion_dual_witness(H, fail_row)
            w_orig_core = {peel.core_orig_rows[P[i]]: y_p[i] for i in range(r) if y_p[i] != 0}
            y_full = _replay_ops_dual_map(peel.ops_log, w_orig_core)
            dual_t = (y_full, mod_m)
        return TorsorResult(
            status="UNSAT_TORSION",
            ring="Z",
            rank_q=peel.peeled_rank + r,
            peeled_rank=peel.peeled_rank,
            core_shape=(m_c, n_c),
            max_bits=max_bits,
            torsion_cert=(h_ii, rem),
            dual_torsion_witness=dual_t,
            pivot_rows_core=P,
            pivot_cols_core=J,
            prescreen_agreed=prescreen_agreed,
            double_det_G=G,
            single_det_D1_bits=d1_bits,
        )

    x_full = None
    if want_witness:
        sel_cols_data = [col_vecs.get(j, [0] * r) for j in generating_cols]
        sol_dict = _reconstruct_integral_witness_core(sel_cols_data, generating_cols, c_P)
        assert sol_dict is not None
        x_core = [0] * n_c
        for col_idx, val in sol_dict.items():
            x_core[col_idx] = val
        x_full = _backsub_peeled(A.ncols, peel.core_orig_cols, x_core, peel.backsub_stack, den=1)

    return TorsorResult(
        status="SAT_INTEGRAL",
        ring="Z",
        rank_q=peel.peeled_rank + r,
        peeled_rank=peel.peeled_rank,
        core_shape=(m_c, n_c),
        max_bits=max_bits,
        x_int=x_full,
        pivot_rows_core=P,
        pivot_cols_core=J,
        prescreen_agreed=prescreen_agreed,
        double_det_G=G,
        single_det_D1_bits=d1_bits,
    )


def verify_torsor_certificate(
    A: SparseIntMatrix,
    c: Sequence[int],
    res: TorsorResult,
) -> Tuple[bool, str]:
    """Independent zero-trust certificate verifier."""
    if res.status == "SAT_INTEGRAL":
        if res.x_int is None:
            return False, "Missing x_int witness"
        lhs = A.matvec(res.x_int)
        for i in range(A.nrows):
            if lhs[i] != c[i]:
                return False, f"SAT_INTEGRAL witness fails at row {i}: {lhs[i]} != {c[i]}"
        return True, "Verified A @ x_int == c over Z"

    if res.status == "SAT_Q":
        if res.x_q_num is None or res.x_q_den <= 0:
            return False, "Missing or invalid x_q witness"
        lhs = A.matvec(res.x_q_num)
        for i in range(A.nrows):
            if lhs[i] != res.x_q_den * c[i]:
                return False, f"SAT_Q witness fails at row {i}: {lhs[i]} != {res.x_q_den * c[i]}"
        return True, "Verified A @ x_q_num == x_q_den * c over Q"

    if res.status == "UNSAT_FREE_COHOMOLOGY":
        if res.dual_free_witness is None:
            return False, "Missing dual_free_witness"
        w = res.dual_free_witness
        col_sums: Dict[int, int] = {}
        wc = 0
        for r, wr in w.items():
            wc += wr * c[r]
            arow = A.rows.get(r)
            if arow:
                for j, v in arow.items():
                    nv = col_sums.get(j, 0) + wr * v
                    if nv == 0:
                        col_sums.pop(j, None)
                    else:
                        col_sums[j] = nv
        if col_sums:
            return False, f"UNSAT_FREE dual witness fails w^T A == 0 at cols {list(col_sums.keys())[:5]}"
        if wc == 0:
            return False, "UNSAT_FREE dual witness has w^T c == 0"
        return True, f"Verified exact Farkas witness w^T A == 0, w^T c == {wc} != 0"

    if res.status == "UNSAT_TORSION":
        if res.dual_torsion_witness is None:
            return False, "Missing dual_torsion_witness"
        y, M = res.dual_torsion_witness
        if M <= 1:
            return False, f"Invalid torsion modulus M={M}"
        col_sums_mod: Dict[int, int] = {}
        yc = 0
        for r, yr in y.items():
            yc += yr * c[r]
            arow = A.rows.get(r)
            if arow:
                for j, v in arow.items():
                    col_sums_mod[j] = (col_sums_mod.get(j, 0) + yr * v) % M
        bad_cols = [j for j, val in col_sums_mod.items() if val != 0]
        if bad_cols:
            return False, f"UNSAT_TORSION dual witness fails y^T A == 0 (mod {M}) at cols {bad_cols[:5]}"
        if yc % M == 0:
            return False, f"UNSAT_TORSION dual witness has y^T c == 0 (mod {M})"
        return True, f"Verified exact torsion dual witness y^T A == 0 (mod {M}), y^T c == {yc % M} != 0 (mod {M})"

    return False, f"Unknown status {res.status}"


# ==============================================================================
# Exact Smith Normal Form v2.0: DHSW Peeling + Bipartite Blocks +
# Double-Determinant Compression G = gcd(D_1, D_2) + Prime-Power Digit-SNF
# + Iliopoulos Mod-2G Fallback
# ==============================================================================


@dataclass
class SNFResult:
    invariant_factors: List[int]
    rank: int
    torsion_factors: List[int]
    peeled_units: int
    core_blocks: List[Tuple[int, int]]
    max_bits: int
    double_det_G_list: List[int] = field(default_factory=list)
    single_det_D1_bits_list: List[int] = field(default_factory=list)
    used_digit_snf: bool = False


def _normalize_divisibility_chain(raw_factors: List[int]) -> List[int]:
    factors = [abs(x) for x in raw_factors if x != 0]
    n = len(factors)
    for i in range(n):
        for j in range(i + 1, n):
            a, b = factors[i], factors[j]
            if b % a != 0:
                g = math.gcd(a, b)
                factors[i] = g
                factors[j] = (a // g) * b
    return factors


def _peel_snf_sparse(
    A: SparseIntMatrix,
    max_markowitz: int = 4,
    max_bits_fill: int = 48,
) -> Tuple[int, List[int], SparseIntMatrix, int]:
    rows: Dict[int, Dict[int, int]] = {r: dict(row) for r, row in A.rows.items()}
    cols: Dict[int, Set[int]] = {j: set(col) for j, col in A.cols.items()}
    active_rows: Set[int] = set(rows.keys())
    active_cols: Set[int] = set(cols.keys())
    max_bits = A.max_bit_length()
    unit_count = 0
    isolated_factors: List[int] = []

    row_deg1: deque = deque()
    row_deg2: deque = deque()
    for r in active_rows:
        lr = len(rows[r])
        if lr == 1:
            row_deg1.append(r)
        elif lr == 2:
            row_deg2.append(r)
    col_deg1 = deque(j for j in active_cols if len(cols[j]) == 1)

    def peel_unit_pair(r_piv: int, j_piv: int) -> None:
        nonlocal unit_count, max_bits
        piv_val = rows[r_piv][j_piv]
        piv_row = rows[r_piv]
        other_rows = [r2 for r2 in cols[j_piv] if r2 != r_piv]
        for r2 in other_rows:
            r2_map = rows[r2]
            factor = r2_map[j_piv] * piv_val
            for col_k, pv in piv_row.items():
                nv = r2_map.get(col_k, 0) - factor * pv
                if nv == 0:
                    if col_k in r2_map:
                        del r2_map[col_k]
                        cols[col_k].discard(r2)
                        if col_k in active_cols and len(cols[col_k]) == 1:
                            col_deg1.append(col_k)
                else:
                    r2_map[col_k] = nv
                    bl = abs(nv).bit_length()
                    if bl > max_bits:
                        max_bits = bl
                    cols.setdefault(col_k, set()).add(r2)
            lr2 = len(r2_map)
            if lr2 == 0:
                active_rows.discard(r2)
                del rows[r2]
            elif lr2 == 1:
                row_deg1.append(r2)
            elif lr2 == 2:
                row_deg2.append(r2)

        for col_k in list(piv_row.keys()):
            cols[col_k].discard(r_piv)
            if col_k != j_piv and col_k in active_cols:
                d = len(cols[col_k])
                if d == 1:
                    col_deg1.append(col_k)
                elif d == 0:
                    active_cols.discard(col_k)
                    cols.pop(col_k, None)
        del rows[r_piv]
        active_rows.discard(r_piv)
        active_cols.discard(j_piv)
        cols.pop(j_piv, None)
        unit_count += 1

    while True:
        progress = False
        while row_deg1 or col_deg1:
            while row_deg1:
                r = row_deg1.popleft()
                if r not in active_rows:
                    continue
                rmap = rows.get(r)
                if not rmap:
                    active_rows.discard(r)
                    continue
                if len(rmap) != 1:
                    continue
                j, v = next(iter(rmap.items()))
                if v == 1 or v == -1:
                    for r2 in list(cols[j]):
                        if r2 == r:
                            continue
                        del rows[r2][j]
                        lr2 = len(rows[r2])
                        if lr2 == 0:
                            del rows[r2]
                            active_rows.discard(r2)
                        elif lr2 == 1:
                            row_deg1.append(r2)
                        elif lr2 == 2:
                            row_deg2.append(r2)
                    del rows[r]
                    active_rows.discard(r)
                    active_cols.discard(j)
                    cols.pop(j, None)
                    unit_count += 1
                    progress = True
                elif len(cols[j]) == 1:
                    isolated_factors.append(abs(v))
                    del rows[r]
                    active_rows.discard(r)
                    active_cols.discard(j)
                    cols.pop(j, None)
                    progress = True

            while col_deg1:
                j = col_deg1.popleft()
                if j not in active_cols:
                    continue
                cset = cols.get(j)
                if not cset:
                    active_cols.discard(j)
                    continue
                if len(cset) != 1:
                    continue
                r = next(iter(cset))
                if r not in active_rows:
                    continue
                v = rows[r].get(j, 0)
                if v == 1 or v == -1:
                    for col_k in list(rows[r].keys()):
                        cols[col_k].discard(r)
                        if col_k != j and col_k in active_cols:
                            d = len(cols[col_k])
                            if d == 1:
                                col_deg1.append(col_k)
                            elif d == 0:
                                active_cols.discard(col_k)
                                cols.pop(col_k, None)
                    del rows[r]
                    active_rows.discard(r)
                    active_cols.discard(j)
                    cols.pop(j, None)
                    unit_count += 1
                    progress = True
                elif len(rows[r]) == 1:
                    isolated_factors.append(abs(v))
                    del rows[r]
                    active_rows.discard(r)
                    active_cols.discard(j)
                    cols.pop(j, None)
                    progress = True

        while row_deg2 and not row_deg1 and not col_deg1:
            r = row_deg2.popleft()
            if r not in active_rows:
                continue
            rmap = rows.get(r)
            if not rmap or len(rmap) != 2:
                continue
            items = list(rmap.items())
            (j1, v1), (j2, v2) = items[0], items[1]
            u1, u2 = (v1 == 1 or v1 == -1), (v2 == 1 or v2 == -1)
            if u1 and u2:
                cand_j, other_v = (j1, v2) if len(cols[j1]) <= len(cols[j2]) else (j2, v1)
            elif u1:
                cand_j, other_v = j1, v2
            elif u2:
                cand_j, other_v = j2, v1
            else:
                continue
            ob = abs(other_v).bit_length()
            if ob > 1:
                if ob > max_bits_fill:
                    continue
                if any(r2 != r and abs(rows[r2][cand_j]).bit_length() + ob > max_bits_fill for r2 in cols[cand_j]):
                    continue
            peel_unit_pair(r, cand_j)
            progress = True
            if row_deg1 or col_deg1:
                break

        if progress:
            continue
        if not active_rows or not active_cols:
            break

        best_piv: Optional[Tuple[int, int]] = None
        best_score = max_markowitz + 1
        checked = 0
        for j in active_cols:
            cdeg = len(cols[j])
            if cdeg == 0 or cdeg - 1 > best_score:
                continue
            for r in cols[j]:
                v = rows[r][j]
                if v != 1 and v != -1:
                    continue
                rdeg = len(rows[r])
                score = (rdeg - 1) * (cdeg - 1)
                if score >= best_score:
                    continue
                rmax = max(abs(x).bit_length() for x in rows[r].values())
                if rmax > max_bits_fill:
                    continue
                if any(r2 != r and abs(rows[r2][j]).bit_length() + rmax > max_bits_fill for r2 in cols[j]):
                    continue
                best_score = score
                best_piv = (r, j)
                if best_score <= 1:
                    break
            if best_score <= 1:
                break
            if best_piv is not None:
                checked += 1
                if checked >= 64:
                    break

        if best_piv is not None:
            peel_unit_pair(best_piv[0], best_piv[1])
            progress = True
        if not progress:
            break

    rem_rows = sorted(active_rows)
    rem_cols = sorted(j for j in active_cols if cols.get(j))
    c_map = {oj: nj for nj, oj in enumerate(rem_cols)}
    core = SparseIntMatrix(len(rem_rows), len(rem_cols))
    for nr, orow in enumerate(rem_rows):
        for oj, v in rows[orow].items():
            core.set_entry(nr, c_map[oj], v)
    return unit_count, isolated_factors, core, max_bits


def _bipartite_blocks(A: SparseIntMatrix) -> List[SparseIntMatrix]:
    visited_r: Set[int] = set()
    visited_c: Set[int] = set()
    blocks: List[SparseIntMatrix] = []
    for r0 in sorted(A.rows.keys()):
        if r0 in visited_r:
            continue
        comp_r, comp_c = [], []
        q_r = deque([r0])
        visited_r.add(r0)
        while q_r:
            r = q_r.popleft()
            comp_r.append(r)
            for j in A.rows.get(r, ()):
                if j not in visited_c:
                    visited_c.add(j)
                    comp_c.append(j)
                    for r2 in A.cols.get(j, ()):
                        if r2 not in visited_r:
                            visited_r.add(r2)
                            q_r.append(r2)
        comp_r.sort()
        comp_c.sort()
        c_map = {oj: nj for nj, oj in enumerate(comp_c)}
        blk = SparseIntMatrix(len(comp_r), len(comp_c))
        for nr, orow in enumerate(comp_r):
            for oj, v in A.rows[orow].items():
                blk.set_entry(nr, c_map[oj], v)
        blocks.append(blk)
    return blocks


def _snf_mod_m_dense(B_in: List[List[int]], rank_r: int, D: int) -> Tuple[List[int], int]:
    """Iliopoulos Modulo-2D exact Smith Normal Form on dense p x q block of rank r."""
    if rank_r == 0:
        return [], 0
    if D == 1:
        return [1] * rank_r, 1

    M = 2 * D
    p = len(B_in)
    q = len(B_in[0])
    B = [[v % M for v in row] for row in B_in]
    max_bits = M.bit_length()

    for k in range(rank_r):
        while True:
            best_i = -1
            best_j = -1
            best_g = M + 1
            best_v = M + 1
            for i in range(k, p):
                row_i = B[i]
                for j in range(k, q):
                    v = row_i[j]
                    if v != 0:
                        g = math.gcd(v, M)
                        if g < best_g or (g == best_g and v < best_v):
                            best_g, best_v, best_i, best_j = g, v, i, j
                            if g == 1 and v == 1:
                                break
                if best_g == 1 and best_v == 1:
                    break

            assert best_i != -1
            if best_i != k:
                B[k], B[best_i] = B[best_i], B[k]
            if best_j != k:
                for i in range(p):
                    B[i][k], B[i][best_j] = B[i][best_j], B[i][k]

            cleared = False
            while not cleared:
                cleared = True
                for i in range(k + 1, p):
                    b = B[i][k]
                    if b == 0:
                        continue
                    cleared = False
                    a = B[k][k]
                    if b % a == 0:
                        mul = b // a
                        row_k, row_i = B[k], B[i]
                        for j in range(k, q):
                            row_i[j] = (row_i[j] - mul * row_k[j]) % M
                    else:
                        g, s, t = xgcd(a, b)
                        a_g, b_g = a // g, b // g
                        row_k, row_i = B[k], B[i]
                        for j in range(k, q):
                            rk, ri = row_k[j], row_i[j]
                            row_k[j] = (s * rk + t * ri) % M
                            row_i[j] = (-b_g * rk + a_g * ri) % M

                for j in range(k + 1, q):
                    b = B[k][j]
                    if b == 0:
                        continue
                    cleared = False
                    a = B[k][k]
                    if b % a == 0:
                        mul = b // a
                        for i in range(k, p):
                            B[i][j] = (B[i][j] - mul * B[i][k]) % M
                    else:
                        g, s, t = xgcd(a, b)
                        a_g, b_g = a // g, b // g
                        for i in range(k, p):
                            ak, aj = B[i][k], B[i][j]
                            B[i][k] = (s * ak + t * aj) % M
                            B[i][j] = (-b_g * ak + a_g * aj) % M

            piv = math.gcd(B[k][k], M)
            B[k][k] = piv

            bad_i = -1
            for i in range(k + 1, p):
                row_i = B[i]
                for j in range(k + 1, q):
                    if row_i[j] % piv != 0:
                        bad_i = i
                        break
                if bad_i != -1:
                    break
            if bad_i == -1:
                break
            row_k, row_bad = B[k], B[bad_i]
            for j in range(k + 1, q):
                row_k[j] = (row_k[j] + row_bad[j]) % M

    return [B[k][k] for k in range(rank_r)], max_bits


def compute_snf(
    A: SparseIntMatrix,
    use_double_det: bool = True,
    crt_rank_threshold: int = 32,
) -> SNFResult:
    """Compute exact Smith Normal Form v2.0 of sparse A over Z.

    Pipeline:
    1. DHSW +/-1 unit-pivot, degree-1 & degree-2 contraction peeling
    2. Bipartite connected-component block decomposition
    3. Rank & minor extraction (61-bit double-prime mod pre-screen for r > threshold,
       verified exact via Hadamard CRT; Markowitz + Bareiss for small cores)
    4. Double-Determinant lattice compression G = gcd(D_1, D_2)
    5. Prime-Power Local Sparse Digit-SNF (for factorable G on unpeelable cores) or
       Iliopoulos Modulo-2G dense exact SNF fallback!
    """
    units, isolated, core, max_bits = _peel_snf_sparse(A)
    raw_factors: List[int] = [1] * units + isolated
    blocks = _bipartite_blocks(core)
    block_shapes: List[Tuple[int, int]] = []
    g_list: List[int] = []
    d1_bits_list: List[int] = []
    used_digit = False

    for blk in blocks:
        block_shapes.append((blk.nrows, blk.ncols))
        # Fast rank & initial minor extraction
        use_fast_mod = (
            use_double_det
            and min(blk.nrows, blk.ncols) > crt_rank_threshold
            and blk.max_bit_length() < 60
        )
        P: List[int] = []
        J: List[int] = []
        if use_fast_mod:
            z_rhs = [0] * blk.nrows
            r1, _, P1, J1 = mod_prescreen_torsor(blk, z_rhs, PRIME_1)
            r2, _, _, _ = mod_prescreen_torsor(blk, z_rhs, PRIME_2)
            # If full row or col rank is certified by D1 > 0, no exact Markowitz rank re-check needed!
            if r1 == r2 and (r1 == blk.nrows or r1 == blk.ncols):
                P, J = P1, J1
            else:
                _, P, J, _, m_bits = markowitz_q_phase1(blk, z_rhs, want_dual_witness=False)
                if m_bits > max_bits:
                    max_bits = m_bits
        else:
            _, P, J, _, m_bits = markowitz_q_phase1(blk, [0] * blk.nrows, want_dual_witness=False)
            if m_bits > max_bits:
                max_bits = m_bits

        r_blk = len(P)
        if r_blk == 0:
            continue

        # Compute exact D_1 and Double-Determinant G = gcd(D_1, D_2)
        if r_blk <= crt_rank_threshold and not (use_double_det and blk.ncols > r_blk and r_blk > 20):
            col_map = {oj: idx for idx, oj in enumerate(J)}
            minor = [[0] * r_blk for _ in range(r_blk)]
            for i, orig_r in enumerate(P):
                for oj, v in blk.rows.get(orig_r, {}).items():
                    cj = col_map.get(oj)
                    if cj is not None:
                        minor[i][cj] = v
            det_val, b_bits = bareiss_det_dense(minor)
            if b_bits > max_bits:
                max_bits = b_bits
            D1 = abs(det_val)
            assert D1 > 0
            if use_double_det and D1 > 1 and (blk.nrows > r_blk or blk.ncols > r_blk):
                G, _, _, dd_bits = double_det_lattice_bound(
                    blk, P, J, allow_row_variation=True, D1_known=D1
                )
                if dd_bits > max_bits:
                    max_bits = dd_bits
            else:
                G = D1
        else:
            if use_double_det:
                G, D1, _, dd_bits = double_det_lattice_bound(blk, P, J, allow_row_variation=True)
                if dd_bits > max_bits:
                    max_bits = dd_bits
            else:
                # Single-minor exact CRT determinant (for v1 vs v2 head-to-head benchmark!)
                D1, _, c_bits = sparse_minor_crt_det_and_adj_solve(blk, P, J)
                G = D1
                if c_bits > max_bits:
                    max_bits = c_bits

        assert D1 > 0 and G > 0
        g_list.append(G)
        d1_bits_list.append(D1.bit_length())

        if G == 1:
            raw_factors.extend([1] * r_blk)
            continue

        # Try Prime-Power Local Sparse Digit-SNF (massive speedup on unpeelable cores & composite torsion!)
        pp = factor_prime_powers(G) if (use_double_det and (r_blk > 12 or G > 1)) else None
        if pp is not None and len(pp) > 0:
            used_digit = True
            combined = [1] * r_blk
            for q, exp_e in pp:
                local_factors = _snf_prime_power_sparse(blk, r_blk, q, exp_e)
                q_bits = (q ** (exp_e + 1)).bit_length()
                if q_bits > max_bits:
                    max_bits = q_bits
                for i in range(r_blk):
                    combined[i] *= local_factors[i]
            raw_factors.extend(combined)
        else:
            blk_factors, s_bits = _snf_mod_m_dense(blk.to_dense(), r_blk, G)
            if s_bits > max_bits:
                max_bits = s_bits
            raw_factors.extend(blk_factors)

    inv_factors = _normalize_divisibility_chain(raw_factors)
    torsion = [d for d in inv_factors if d > 1]
    return SNFResult(
        invariant_factors=inv_factors,
        rank=len(inv_factors),
        torsion_factors=torsion,
        peeled_units=units,
        core_blocks=block_shapes,
        max_bits=max_bits,
        double_det_G_list=g_list,
        single_det_D1_bits_list=d1_bits_list,
        used_digit_snf=used_digit,
    )


def compute_exact_rref_rows(
    A: SparseIntMatrix,
    c: Sequence[int],
) -> Tuple[bool, List[Tuple[Dict[int, int], int]], List[int]]:
    """Compute exact primitive integer Reduced Row Echelon Form (RREF) of [A | c] over Q."""
    m, n = A.nrows, A.ncols
    rhs_col = n
    rows: List[Dict[int, int]] = []
    for r in range(m):
        rd = dict(A.rows.get(r, {}))
        if c[r] != 0:
            rd[rhs_col] = c[r]
        if rd:
            rows.append(rd)

    piv_rows: List[Dict[int, int]] = []
    piv_cols: List[int] = []

    for col in range(n):
        best_idx = -1
        best_abs = 1 << 1000
        for idx in range(len(rows)):
            v = rows[idx].get(col, 0)
            if v != 0 and abs(v) < best_abs:
                best_abs = abs(v)
                best_idx = idx
        if best_idx == -1:
            continue

        piv_row = rows.pop(best_idx)
        if piv_row[col] < 0:
            piv_row = {k: -v for k, v in piv_row.items()}
        piv_val = piv_row[col]

        def _elim_row(target: Dict[int, int]) -> Dict[int, int]:
            v = target.get(col, 0)
            if v == 0:
                return target
            g = math.gcd(piv_val, abs(v))
            m_t, m_p = piv_val // g, v // g
            out: Dict[int, int] = {}
            for k, tv in target.items():
                nv = tv * m_t - m_p * piv_row.get(k, 0)
                if nv != 0:
                    out[k] = nv
            for k, pv in piv_row.items():
                if k not in target:
                    nv = -m_p * pv
                    if nv != 0:
                        out[k] = nv
            if out:
                rg = _gcd_values(out.values())
                if rg > 1:
                    out = {k: val // rg for k, val in out.items()}
            return out

        rows = [er for row in rows if (er := _elim_row(row))]
        for p_idx in range(len(piv_rows)):
            piv_rows[p_idx] = _elim_row(piv_rows[p_idx])
            pcol = piv_cols[p_idx]
            if piv_rows[p_idx].get(pcol, 0) < 0:
                piv_rows[p_idx] = {k: -v for k, v in piv_rows[p_idx].items()}

        piv_rows.append(piv_row)
        piv_cols.append(col)

    for row in rows:
        if rhs_col in row and len(row) == 1:
            return False, [], piv_cols

    out_eqs: List[Tuple[Dict[int, int], int]] = []
    for pr in piv_rows:
        out_eqs.append(({k: v for k, v in pr.items() if k != rhs_col}, pr.get(rhs_col, 0)))
    return True, out_eqs, piv_cols


# ==============================================================================
# SECTION 2: IEEE-754 FLOAT64 BASELINE SIMULATOR
# ==============================================================================

FLOAT64_EPS = 2.220446049250313e-16  # IEEE-754 binary64 machine epsilon (2^-52)


def _hypot(a: float, b: float) -> float:
    return math.hypot(a, b)


def _pythag_sign(a: float, b: float) -> float:
    return abs(a) if b >= 0.0 else -abs(a)


# ==============================================================================
# 1. Symmetric Eigensolver (Householder Tridiagonalization + Implicit QL)
# ==============================================================================


def symmetric_eigenvalues_float64(mat: Sequence[Sequence[float]]) -> List[float]:
    """Compute all eigenvalues of a real symmetric matrix in IEEE-754 float64.

    Uses Householder tridiagonalization (tred1) followed by implicit Wilkinson-shift QL (tql1).
    Returns eigenvalues sorted ascending.
    """
    n = len(mat)
    if n == 0:
        return []
    if n == 1:
        return [float(mat[0][0])]

    a = [[float(v) for v in row] for row in mat]
    d = [0.0] * n
    e = [0.0] * n

    # Householder reduction to symmetric tridiagonal form (tred1)
    for i in range(n - 1, 0, -1):
        l = i - 1
        h = 0.0
        scale = 0.0
        if l > 0:
            row_i = a[i]
            for k in range(l + 1):
                scale += abs(row_i[k])
            if scale == 0.0:
                e[i] = row_i[l]
            else:
                inv_scale = 1.0 / scale
                for k in range(l + 1):
                    row_i[k] *= inv_scale
                    h += row_i[k] * row_i[k]
                f = row_i[l]
                g = -math.sqrt(h) if f >= 0.0 else math.sqrt(h)
                e[i] = scale * g
                h -= f * g
                row_i[l] = f - g
                f = 0.0
                for j in range(l + 1):
                    g = 0.0
                    row_j = a[j]
                    for k in range(j + 1):
                        g += row_j[k] * row_i[k]
                    for k in range(j + 1, l + 1):
                        g += a[k][j] * row_i[k]
                    e[j] = g / h
                    f += e[j] * row_i[j]
                hh = f / (h + h)
                for j in range(l + 1):
                    f = row_i[j]
                    g = e[j] - hh * f
                    e[j] = g
                    row_j = a[j]
                    for k in range(j + 1):
                        row_j[k] -= f * e[k] + g * row_i[k]
        else:
            e[i] = a[i][l]
        d[i] = h

    for i in range(n):
        d[i] = a[i][i]

    # Shift e so e[i] is subdiagonal between d[i] and d[i+1], e[n-1] = 0
    for i in range(1, n):
        e[i - 1] = e[i]
    e[n - 1] = 0.0

    # Implicit Wilkinson-shift QL algorithm (tql1)
    for l in range(n):
        iters = 0
        while True:
            # Find small subdiagonal element
            m = l
            while m < n - 1:
                dd = abs(d[m]) + abs(d[m + 1])
                if abs(e[m]) + dd == dd:
                    break
                m += 1
            if m == l:
                break
            iters += 1
            if iters > 60:
                break
            g = (d[l + 1] - d[l]) / (2.0 * e[l])
            r = _hypot(g, 1.0)
            g = d[m] - d[l] + e[l] / (g + _pythag_sign(r, g))
            s = 1.0
            c = 1.0
            p = 0.0
            for i in range(m - 1, l - 1, -1):
                f = s * e[i]
                b = c * e[i]
                r = _hypot(f, g)
                e[i + 1] = r
                if r == 0.0:
                    d[i + 1] -= p
                    e[m] = 0.0
                    break
                s = f / r
                c = g / r
                g = d[i + 1] - p
                r = (d[i] - g) * s + 2.0 * c * b
                p = s * r
                d[i + 1] = g + p
                g = c * r - b
            else:
                d[l] -= p
                e[l] = g
                e[m] = 0.0

    d.sort()
    return d


# ==============================================================================
# 2. Direct Golub-Kahan-Reinsch SVD (No A^T A Squaring!)
# ==============================================================================


def svd_golub_kahan_float64(
    mat: Sequence[Sequence[float]],
    rhs: Optional[Sequence[float]] = None,
) -> Tuple[List[float], Optional[List[float]]]:
    """Direct IEEE-754 float64 SVD via Householder bidiagonalization + Golub-Kahan implicit QR.

    Computes all singular values sorted descending WITHOUT forming A^T A.
    If `rhs` (length m) is provided, simultaneously projects `b = U^T rhs` (length m)
    so exact SVD least-squares residuals can be evaluated for any rank cutoff!
    """
    m_orig = len(mat)
    if m_orig == 0:
        return [], ([] if rhs is not None else None)
    n_orig = len(mat[0])
    if n_orig == 0:
        return [], ([float(v) for v in rhs] if rhs is not None else None)

    transposed = False
    if m_orig < n_orig:
        # Transpose so A is tall (m >= n); left singular vectors of original A
        # are right singular vectors of A^T!
        transposed = True
        m, n = n_orig, m_orig
        A = [[float(mat[j][i]) for j in range(m_orig)] for i in range(n_orig)]
    else:
        m, n = m_orig, n_orig
        A = [[float(v) for v in row] for row in mat]

    b_vec: Optional[List[float]] = [float(v) for v in rhs] if rhs is not None else None

    q = [0.0] * n  # diagonal of bidiagonal B
    e = [0.0] * n  # superdiagonal of bidiagonal B (e[0] = 0, e[k] connects q[k-1] and q[k])

    # Step 1: Householder reduction to upper bidiagonal form
    g = 0.0
    scale = 0.0
    anorm = 0.0
    for i in range(n):
        l = i + 1
        e[i] = scale * g
        g = 0.0
        s = 0.0
        scale = 0.0
        if i < m:
            for k in range(i, m):
                scale += abs(A[k][i])
            if scale != 0.0:
                inv_sc = 1.0 / scale
                for k in range(i, m):
                    A[k][i] *= inv_sc
                    s += A[k][i] * A[k][i]
                f = A[i][i]
                g = -math.sqrt(s) if f >= 0.0 else math.sqrt(s)
                h = f * g - s
                A[i][i] = f - g
                for j in range(l, n):
                    s_col = 0.0
                    for k in range(i, m):
                        s_col += A[k][i] * A[k][j]
                    f_col = s_col / h
                    for k in range(i, m):
                        A[k][j] += f_col * A[k][i]
                # If not transposed, apply left Householder reflection to b_vec!
                if b_vec is not None and not transposed:
                    s_b = 0.0
                    for k in range(i, m):
                        s_b += A[k][i] * b_vec[k]
                    f_b = s_b / h
                    for k in range(i, m):
                        b_vec[k] += f_b * A[k][i]
                for k in range(i, m):
                    A[k][i] *= scale
        q[i] = scale * g

        g = 0.0
        s = 0.0
        scale = 0.0
        if i < m and i != n - 1:
            row_i = A[i]
            for k in range(l, n):
                scale += abs(row_i[k])
            if scale != 0.0:
                inv_sc = 1.0 / scale
                for k in range(l, n):
                    row_i[k] *= inv_sc
                    s += row_i[k] * row_i[k]
                f = row_i[l]
                g = -math.sqrt(s) if f >= 0.0 else math.sqrt(s)
                h = f * g - s
                row_i[l] = f - g
                for j in range(l, m):
                    row_j = A[j]
                    s_row = 0.0
                    for k in range(l, n):
                        s_row += row_j[k] * row_i[k]
                    f_row = s_row / h
                    for k in range(l, n):
                        row_j[k] += f_row * row_i[k]
                # If transposed, apply right Householder reflection to b_vec (length n == m_orig)!
                if b_vec is not None and transposed:
                    s_b = 0.0
                    for k in range(l, n):
                        s_b += b_vec[k] * row_i[k]
                    f_b = s_b / h
                    for k in range(l, n):
                        b_vec[k] += f_b * row_i[k]
                for k in range(l, n):
                    row_i[k] *= scale
        anorm = max(anorm, abs(q[i]) + abs(e[i]))

    # Step 2: Golub-Kahan implicit QR diagonalization of bidiagonal (q, e)
    for k in range(n - 1, -1, -1):
        for _its in range(80):
            flag = True
            l_split = 0
            for l in range(k, -1, -1):
                l_split = l
                nm = l - 1
                if abs(e[l]) + anorm == anorm:
                    flag = False
                    break
                if nm >= 0 and abs(q[nm]) + anorm == anorm:
                    break
            if flag:
                # Cancellation of e[l_split] if q[l_split - 1] == 0
                c = 0.0
                s = 1.0
                nm = l_split - 1
                for i in range(l_split, k + 1):
                    f = s * e[i]
                    e[i] = c * e[i]
                    if abs(f) + anorm == anorm:
                        break
                    g_val = q[i]
                    h = _hypot(f, g_val)
                    q[i] = h
                    c = g_val / h
                    s = -f / h
                    if b_vec is not None and not transposed:
                        y = b_vec[nm]
                        z = b_vec[i]
                        b_vec[nm] = y * c + z * s
                        b_vec[i] = -y * s + z * c

            z = q[k]
            if l_split == k:
                if z < 0.0:
                    q[k] = -z
                    if b_vec is not None and transposed:
                        b_vec[k] = -b_vec[k]
                break

            # Wilkinson shift from bottom 2x2 minor of B^T B
            x = q[l_split]
            nm = k - 1
            y = q[nm]
            g_val = e[nm]
            h = e[k]
            f = ((y - z) * (y + z) + (g_val - h) * (g_val + h)) / (2.0 * h * y) if (h * y != 0.0) else 0.0
            g_val = _hypot(f, 1.0)
            denom = f + _pythag_sign(g_val, f)
            f = ((x - z) * (x + z) + h * ((y / denom if denom != 0.0 else 0.0) - h)) / x if x != 0.0 else 0.0

            # Next QR transformation (chasing the bulge)
            c = 1.0
            s = 1.0
            for j in range(l_split, nm + 1):
                i = j + 1
                g_val = e[i]
                y = q[i]
                h = s * g_val
                g_val = c * g_val
                z = _hypot(f, h)
                e[j] = z
                if z != 0.0:
                    c = f / z
                    s = h / z
                else:
                    c = 1.0
                    s = 0.0
                f = x * c + g_val * s
                g_val = g_val * c - x * s
                h = y * s
                y = y * c
                # Right Givens rotation on cols (j, i) of B
                if b_vec is not None and transposed:
                    bj = b_vec[j]
                    bi = b_vec[i]
                    b_vec[j] = bj * c + bi * s
                    b_vec[i] = -bj * s + bi * c

                z = _hypot(f, h)
                q[j] = z
                if z != 0.0:
                    c = f / z
                    s = h / z
                else:
                    c = 1.0
                    s = 0.0
                f = c * g_val + s * y
                x = -s * g_val + c * y
                # Left Givens rotation on rows (j, i) of B
                if b_vec is not None and not transposed:
                    bj = b_vec[j]
                    bi = b_vec[i]
                    b_vec[j] = bj * c + bi * s
                    b_vec[i] = -bj * s + bi * c

            e[l_split] = 0.0
            e[k] = f
            q[k] = x

    # Sort singular values descending, permuting first n entries of b_vec in lockstep!
    order = sorted(range(n), key=lambda idx: abs(q[idx]), reverse=True)
    sigmas = [abs(q[idx]) for idx in order]
    if b_vec is not None:
        b_sorted = [b_vec[idx] for idx in order]
        if not transposed and m > n:
            b_sorted.extend(b_vec[n:])
        return sigmas, b_sorted
    return sigmas, None


# ==============================================================================
# 3. High-Level Float64 Evaluators & l_2 Hodge Harmonic Blame
# ==============================================================================


@dataclass
class Float64LaplacianReport:
    min_eig: float
    max_eig: float
    apparent_h0_dim_atol: int
    apparent_h0_dim_rel: int
    atol: float
    rel_tol: float
    verdict_homogeneous_contradiction: bool  # True if dim H^0 == 0 (no global section)


@dataclass
class Float64SVDTorsorReport:
    sigma_min: float
    sigma_max: float
    cond_est: float
    rank_svd_std: int        # tol = max(m, n) * eps * sigma_max
    rank_svd_atol: int       # tol = atol (1e-12)
    apparent_h1_std: int     # m - rank_svd_std
    apparent_h1_atol: int    # m - rank_svd_atol
    residual_std: float      # ||A x* - c||_2 under standard SVD cutoff
    residual_atol: float     # ||A x* - c||_2 under atol cutoff
    dirichlet_energy: float  # ||A x* - c||_2^2
    verdict_unsat_std: bool  # residual_std > max(atol, 1e-9 * max(1, ||c||))?
    verdict_unsat_atol: bool # residual_atol > atol


def sparse_to_float_dense(nrows: int, ncols: int, rows: Dict[int, Dict[int, int]]) -> List[List[float]]:
    mat = [[0.0] * ncols for _ in range(nrows)]
    for r, row in rows.items():
        target = mat[r]
        for c, v in row.items():
            target[c] = float(v)
    return mat


def compute_L0_dense(A_dense: Sequence[Sequence[float]]) -> List[List[float]]:
    """Compute float64 sheaf Laplacian L_0 = A^T A explicitly."""
    m = len(A_dense)
    n = len(A_dense[0]) if m > 0 else 0
    L0 = [[0.0] * n for _ in range(n)]
    for r in range(m):
        row = A_dense[r]
        nz = [(j, row[j]) for j in range(n) if row[j] != 0.0]
        for j, vj in nz:
            lj = L0[j]
            for k, vk in nz:
                lj[k] += vj * vk
    return L0


def evaluate_float64_laplacian(
    A_dense: Sequence[Sequence[float]],
    atol: float = 1e-12,
) -> Float64LaplacianReport:
    """Evaluate homogeneous sheaf Laplacian L_0 = (delta^0)^T delta^0 in IEEE-754 float64."""
    L0 = compute_L0_dense(A_dense)
    n = len(L0)
    if n == 0:
        return Float64LaplacianReport(0.0, 0.0, 0, 0, atol, atol, False)
    eigs = symmetric_eigenvalues_float64(L0)
    min_eig = eigs[0]
    max_eig = max(abs(eigs[-1]), abs(eigs[0]))
    rel_tol = max(atol, n * FLOAT64_EPS * max_eig)
    h0_atol = sum(1 for ev in eigs if ev <= atol)
    h0_rel = sum(1 for ev in eigs if ev <= rel_tol)
    return Float64LaplacianReport(
        min_eig=min_eig,
        max_eig=max_eig,
        apparent_h0_dim_atol=h0_atol,
        apparent_h0_dim_rel=h0_rel,
        atol=atol,
        rel_tol=rel_tol,
        verdict_homogeneous_contradiction=(h0_atol == 0),
    )


def evaluate_float64_svd_torsor(
    A_dense: Sequence[Sequence[float]],
    c_float: Sequence[float],
    atol: float = 1e-12,
) -> Float64SVDTorsorReport:
    """Evaluate inhomogeneous affine torsor A x = c via direct Golub-Kahan float64 SVD."""
    m = len(A_dense)
    n = len(A_dense[0]) if m > 0 else 0
    if m == 0 or n == 0:
        res_norm = math.sqrt(sum(v * v for v in c_float))
        return Float64SVDTorsorReport(
            sigma_min=0.0,
            sigma_max=0.0,
            cond_est=math.inf,
            rank_svd_std=0,
            rank_svd_atol=0,
            apparent_h1_std=m,
            apparent_h1_atol=m,
            residual_std=res_norm,
            residual_atol=res_norm,
            dirichlet_energy=res_norm * res_norm,
            verdict_unsat_std=(res_norm > atol),
            verdict_unsat_atol=(res_norm > atol),
        )

    sigmas, b_proj = svd_golub_kahan_float64(A_dense, c_float)
    assert b_proj is not None
    p = len(sigmas)
    s_max = sigmas[0] if p > 0 else 0.0
    s_min = sigmas[-1] if p > 0 else 0.0
    cond = (s_max / s_min) if s_min > 0.0 else math.inf

    tol_std = max(m, n) * FLOAT64_EPS * s_max
    rank_std = sum(1 for s in sigmas if s > tol_std)
    rank_atol = sum(1 for s in sigmas if s > atol)

    # Residual squared = sum_{i >= rank} b_proj[i]^2 (for i in range(rank, m))
    e_std = sum(b_proj[i] * b_proj[i] for i in range(rank_std, m))
    e_atol = sum(b_proj[i] * b_proj[i] for i in range(rank_atol, m))
    r_std = math.sqrt(e_std)
    r_atol = math.sqrt(e_atol)

    c_norm = math.sqrt(sum(v * v for v in c_float))
    thresh_std = max(atol, max(m, n) * FLOAT64_EPS * max(1.0, c_norm) * 100.0)
    return Float64SVDTorsorReport(
        sigma_min=s_min,
        sigma_max=s_max,
        cond_est=cond,
        rank_svd_std=rank_std,
        rank_svd_atol=rank_atol,
        apparent_h1_std=m - rank_std,
        apparent_h1_atol=m - rank_atol,
        residual_std=r_std,
        residual_atol=r_atol,
        dirichlet_energy=e_std,
        verdict_unsat_std=(r_std > thresh_std),
        verdict_unsat_atol=(r_atol > atol),
    )


def l2_hodge_harmonic_cg(
    nrows: int,
    ncols: int,
    rows: Dict[int, Dict[int, int]],
    c_float: Sequence[float],
    max_iter: int = 2000,
    tol: float = 1e-12,
) -> Tuple[List[float], List[float], float, List[float]]:
    """Solve min_x ||A x - c||_2^2 via Jacobi-preconditioned Conjugate Gradient on A^T A x = A^T c.

    Handles sparse complexes up to 5,000+ edges in pure Python with zero O(n^2) memory!
    Returns (x_star, residual_vec, dirichlet_energy, edge_blame_fractions).
    """
    # Build float sparse rows and column diagonal of A^T A
    f_rows: List[List[Tuple[int, float]]] = [[] for _ in range(nrows)]
    diag = [0.0] * ncols
    rhs = [0.0] * ncols  # A^T c
    for r, rmap in rows.items():
        cr = float(c_float[r])
        lst = [(j, float(v)) for j, v in rmap.items()]
        f_rows[r] = lst
        for j, fv in lst:
            diag[j] += fv * fv
            rhs[j] += fv * cr

    inv_diag = [1.0 / d if d > 1e-30 else 0.0 for d in diag]

    def apply_AtA(v: Sequence[float]) -> List[float]:
        # tmp = A v, out = A^T tmp
        out = [0.0] * ncols
        for r in range(nrows):
            lst = f_rows[r]
            if not lst:
                continue
            acc = 0.0
            for j, fv in lst:
                acc += fv * v[j]
            if acc != 0.0:
                for j, fv in lst:
                    out[j] += fv * acc
        return out

    x = [0.0] * ncols
    r_vec = list(rhs)  # rhs - A^T A x (x=0)
    z = [r_vec[j] * inv_diag[j] for j in range(ncols)]
    p = list(z)
    rz_old = sum(r_vec[j] * z[j] for j in range(ncols))
    rhs_norm = math.sqrt(sum(v * v for v in rhs))
    stop_tol = max(tol * max(1.0, rhs_norm), 1e-15)

    for _ in range(min(max_iter, max(200, 4 * ncols))):
        if math.sqrt(sum(v * v for v in r_vec)) <= stop_tol:
            break
        Ap = apply_AtA(p)
        pAp = sum(p[j] * Ap[j] for j in range(ncols))
        if pAp <= 1e-30:
            break
        alpha = rz_old / pAp
        for j in range(ncols):
            x[j] += alpha * p[j]
            r_vec[j] -= alpha * Ap[j]
        z = [r_vec[j] * inv_diag[j] for j in range(ncols)]
        rz_new = sum(r_vec[j] * z[j] for j in range(ncols))
        if rz_old <= 1e-30:
            break
        beta = rz_new / rz_old
        for j in range(ncols):
            p[j] = z[j] + beta * p[j]
        rz_old = rz_new

    # Compute residual r = c - A x and edge blame fractions
    res = [0.0] * nrows
    energy = 0.0
    for r in range(nrows):
        acc = 0.0
        for j, fv in f_rows[r]:
            acc += fv * x[j]
        diff = float(c_float[r]) - acc
        res[r] = diff
        energy += diff * diff

    if energy > 0.0:
        blame = [(d * d) / energy for d in res]
    else:
        blame = [0.0] * nrows
    return x, res, energy, blame


# ==============================================================================
# SECTION 3: CELLULAR 1-COMPLEX & SIMPLICIAL 2-COMPLEX COHOMOLOGY
# ==============================================================================

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


# ==============================================================================
# SECTION 4: EXACT l_0 QUICKXPLAIN MUS & MCS LOCALIZATION
# ==============================================================================

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


# ==============================================================================
# SECTION 5: LAWVERE-TARSKI LATTICE & CHVATAL-GOMORY HYBRID ENGINE v2.0
# ==============================================================================

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


# ==============================================================================
# SECTION 6: STREAMING PRE-COMMIT SHEAF FIREWALL
# ==============================================================================

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


# ==============================================================================
# SECTION 7: 5-DOMAIN CLAIM COMPILER & FORENSIC AUTOPSY
# ==============================================================================

@dataclass
class ContradictionAutopsy:
    """Structured & human-readable Forensic Contradiction Autopsy Report."""

    domain: str
    title: str
    verdict: str  # "CERTIFIED_CONSISTENT", "CERTIFIED_CONTRADICTION", "OPEN_BUDGET_EXCEEDED"
    total_claims: int
    contradiction_class: Optional[str] = None
    certificate: Dict[str, Any] = field(default_factory=dict)
    verified_witness: Optional[Dict[str, Any]] = None
    mus_claims: List[Dict[str, Any]] = field(default_factory=list)
    mcs_repairs: List[List[str]] = field(default_factory=list)
    elapsed_ms: float = 0.0
    notes: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "domain": self.domain,
            "title": self.title,
            "verdict": self.verdict,
            "total_claims": self.total_claims,
            "contradiction_class": self.contradiction_class,
            "certificate": self.certificate,
            "verified_witness": self.verified_witness,
            "mus_claims": self.mus_claims,
            "mcs_repairs": self.mcs_repairs,
            "elapsed_ms": round(self.elapsed_ms, 3),
            "notes": self.notes,
        }

    def format_report(self) -> str:
        lines: List[str] = [
            "=" * 78,
            f"SHEAF RADAR v2.0 — FORENSIC CONTRADICTION AUTOPSY",
            "=" * 78,
            f"Title   : {self.title}",
            f"Domain  : {self.domain}",
            f"Claims  : {self.total_claims}",
            f"Verdict : {self.verdict}  ({self.elapsed_ms:.2f} ms)",
        ]
        if self.contradiction_class:
            lines.append(f"Class   : {self.contradiction_class}")
        if self.certificate:
            lines.append(f"Cert    : {json.dumps(self.certificate, sort_keys=True)}")
        if self.notes:
            lines.append(f"Notes   : {self.notes}")

        if self.verdict == "CERTIFIED_CONSISTENT" and self.verified_witness is not None:
            preview = list(self.verified_witness.items())[:12]
            lines.append("Witness (verified against 100% of input claims):")
            for k, v in preview:
                lines.append(f"  {k} = {v}")
            if len(self.verified_witness) > 12:
                lines.append(f"  ... ({len(self.verified_witness) - 12} more variables)")

        if self.verdict == "CERTIFIED_CONTRADICTION":
            lines.append(f"\nMinimal Unsatisfiable Subset (MUS — {len(self.mus_claims)} culprit claims):")
            for cl in self.mus_claims:
                cid = cl.get("id", "?")
                op = cl.get("op", "")
                desc = cl.get("description", "")
                lines.append(f"  - [{cid}] ({op}) {desc}")
            if self.mcs_repairs:
                lines.append(f"\nVerified Minimal Repair Suggestions (MCS — deleting any listed set restores consistency):")
                for idx, rep in enumerate(self.mcs_repairs, 1):
                    lines.append(f"  Repair #{idx}: remove claim(s) {rep}")
        lines.append("=" * 78)
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Exact Integer Prime Factorization (Pure Python Stdlib, Zero Floats!)
# ---------------------------------------------------------------------------

def _prime_factors_signed(num: int, den: int) -> Dict[int, int]:
    """Compute exact prime-exponent vector v_p(num / den) for positive integers num, den
    using Miller-Rabin + Pollard-rho (`sparse_exact_v2.factor_prime_powers`)."""
    if num <= 0 or den <= 0:
        raise ValueError(f"Expected positive integers for prime factorization, got {num}/{den}")
    g = math.gcd(num, den)
    num //= g
    den //= g
    exps: Dict[int, int] = {}

    def factor_into(n: int, sign: int) -> None:
        if n <= 1:
            return
        fp = se.factor_prime_powers(n)
        if fp is not None:
            for p, e in fp:
                exps[p] = exps.get(p, 0) + sign * e
            return
        # Fallback for >80-bit cofactors: trial-divide small primes then keep residual cofactor
        rem = n
        for d in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
            if rem % d == 0:
                cnt = 0
                while rem % d == 0:
                    rem //= d
                    cnt += 1
                exps[d] = exps.get(d, 0) + sign * cnt
        if rem > 1:
            exps[rem] = exps.get(rem, 0) + sign

    factor_into(num, +1)
    factor_into(den, -1)
    return {p: e for p, e in exps.items() if e != 0}


# ---------------------------------------------------------------------------
# Shared MUS & MCS Extraction Helper (Zero-Trust Verified!)
# ---------------------------------------------------------------------------

def _extract_mus_and_mcs(
    claims: List[Dict[str, Any]],
    is_unsat_fn: Callable[[Sequence[int]], bool],
    max_repairs: int = 5,
) -> Tuple[List[Dict[str, Any]], List[List[str]]]:
    """Extract verified exact QuickXplain MUS and verified MCS minimal repairs."""
    n = len(claims)
    all_idx = list(range(n))
    mus_rep = quickxplain_mus(all_idx, is_unsat_fn, verify_minimality=True)
    mus_idx = list(mus_rep.mus_ids)
    mus_claims = [claims[i] for i in mus_idx]

    # Single-claim MCS repairs: every single claim in the MUS whose deletion makes the FULL
    # system consistent is a certified size-1 Minimal Correction Subset (MCS)!
    repairs: List[List[str]] = []
    for i in mus_idx:
        if len(repairs) >= max_repairs:
            break
        remaining = [j for j in all_idx if j != i]
        if not is_unsat_fn(remaining):
            repairs.append([str(claims[i].get("id", f"claim_{i}"))])

    # If multiple disjoint contradictions exist (no size-1 MCS), extract a size-k hitting repair
    # greedily from successive MUSes and verify minimality!
    if not repairs and mus_idx:
        removed: List[int] = []
        active = list(all_idx)
        while is_unsat_fn(active) and len(removed) < 6:
            sub_mus = quickxplain_mus(active, is_unsat_fn, verify_minimality=False).mus_ids
            if not sub_mus:
                break
            pick = sub_mus[-1]
            removed.append(pick)
            active = [j for j in active if j != pick]
        if not is_unsat_fn(active):
            # Prune any redundant removal to guarantee minimal MCS!
            minimal_rem: List[int] = []
            for r_i in removed:
                test_active = [j for j in all_idx if j not in removed or j == r_i]
                if is_unsat_fn(test_active):
                    minimal_rem.append(r_i)
            if minimal_rem:
                repairs.append([str(claims[i].get("id", f"claim_{i}")) for i in minimal_rem])
    return mus_claims, repairs


# ---------------------------------------------------------------------------
# Domain 1: Temporal & Periodic Schedules (`temporal_schedule`)
# ---------------------------------------------------------------------------

def _compile_temporal_schedule(spec: Dict[str, Any], t0: float) -> ContradictionAutopsy:
    title = str(spec.get("title", "Temporal Schedule Audit"))
    claims: List[Dict[str, Any]] = list(spec.get("claims", []))
    has_order = any(cl.get("op") in ("precedence", "window") for cl in claims)
    default_lo = int(spec.get("default_lo", -100000))
    default_hi = int(spec.get("default_hi", 100000))

    if not has_order:
        # Pure exact Z-torsor (offsets, anchors, periodic modular clocks)
        def build_and_solve(sub_idx: Sequence[int], want_w: bool = False):
            vmap: Dict[str, int] = {}
            extra_vars: List[str] = []
            sub_cl = [claims[i] for i in sub_idx]
            for cl in sub_cl:
                for k in ("a", "b", "var"):
                    if k in cl:
                        vmap.setdefault(str(cl[k]), len(vmap))
            # Count auxiliary wrap variables for modular_clock
            wrap_col: Dict[int, int] = {}
            for r_i, cl in enumerate(sub_cl):
                if cl.get("op") == "modular_clock":
                    cid = len(vmap) + len(extra_vars)
                    extra_vars.append(f"_wrap_{r_i}")
                    wrap_col[r_i] = cid
            ncols = len(vmap) + len(extra_vars)
            A = se.SparseIntMatrix(len(sub_cl), ncols)
            c = [0] * len(sub_cl)
            for r_i, cl in enumerate(sub_cl):
                op = cl.get("op")
                if op == "offset":
                    A.add_entry(r_i, vmap[str(cl["b"])], 1)
                    A.add_entry(r_i, vmap[str(cl["a"])], -1)
                    c[r_i] = int(cl["delta"])
                elif op == "anchor":
                    A.add_entry(r_i, vmap[str(cl["var"])], 1)
                    c[r_i] = int(cl["value"])
                elif op == "modular_clock":
                    # t[b] - t[a] - M * k = delta
                    A.add_entry(r_i, vmap[str(cl["b"])], 1)
                    A.add_entry(r_i, vmap[str(cl["a"])], -1)
                    A.add_entry(r_i, wrap_col[r_i], -int(cl["modulus"]))
                    c[r_i] = int(cl["delta"])
                else:
                    raise ValueError(f"Unknown temporal_schedule op {op!r}")
            res = se.solve_torsor(A, c, ring="Z", want_witness=want_w)
            return A, c, res, vmap

        all_idx = list(range(len(claims)))
        A, c, res, vmap = build_and_solve(all_idx, want_w=True)
        ok_cert, cert_msg = se.verify_torsor_certificate(A, c, res)
        assert ok_cert, f"Internal certificate failure: {cert_msg}"

        if res.status == "SAT_INTEGRAL":
            assert res.x_int is not None
            wit = {name: int(res.x_int[col]) for name, col in vmap.items()}
            # Independent claim-by-claim witness verification!
            for cl in claims:
                op = cl["op"]
                if op == "offset":
                    assert wit[str(cl["b"])] - wit[str(cl["a"])] == int(cl["delta"])
                elif op == "anchor":
                    assert wit[str(cl["var"])] == int(cl["value"])
                elif op == "modular_clock":
                    assert (wit[str(cl["b"])] - wit[str(cl["a"])] - int(cl["delta"])) % int(cl["modulus"]) == 0
            return ContradictionAutopsy(
                domain="temporal_schedule",
                title=title,
                verdict="CERTIFIED_CONSISTENT",
                total_claims=len(claims),
                certificate={"verified": True, "detail": cert_msg},
                verified_witness=wit,
                elapsed_ms=(time.perf_counter() - t0) * 1000.0,
            )

        mus_claims, mcs_repairs = _extract_mus_and_mcs(
            claims, lambda sub: build_and_solve(sub, want_w=False)[2].status != "SAT_INTEGRAL"
        )
        cert_d: Dict[str, Any] = {"verified": True, "detail": cert_msg}
        if res.torsion_cert is not None:
            cert_d["torsion_mod"] = int(res.torsion_cert[0])
            cert_d["torsion_rem"] = int(res.torsion_cert[1])
        if res.dual_free_witness is not None:
            cert_d["dual_support_size"] = sum(1 for v in res.dual_free_witness.values() if v != 0)
        return ContradictionAutopsy(
            domain="temporal_schedule",
            title=title,
            verdict="CERTIFIED_CONTRADICTION",
            total_claims=len(claims),
            contradiction_class=res.status,
            certificate=cert_d,
            mus_claims=mus_claims,
            mcs_repairs=mcs_repairs,
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )

    # Hybrid Algebraic-Tarski Schedule (includes precedence t_a + gap <= t_b and/or windows!)
    def build_and_solve_tarski(sub_idx: Sequence[int]):
        vmap: Dict[str, int] = {}
        sub_cl = [claims[i] for i in sub_idx]
        for cl in sub_cl:
            for k in ("a", "b", "var"):
                if k in cl:
                    vmap.setdefault(str(cl[k]), len(vmap))
        # Auxiliary variables for precedence slacks and modular wraps
        aux_bounds: List[Tuple[int, int]] = []
        eq_rows: List[Tuple[List[Tuple[int, int]], int]] = []
        ineqs: List[th2.DirectedIntInequality] = []
        var_lo: Dict[int, int] = {col: default_lo for col in vmap.values()}
        var_hi: Dict[int, int] = {col: default_hi for col in vmap.values()}

        for cl in sub_cl:
            op = cl.get("op")
            if op == "offset":
                eq_rows.append(([(vmap[str(cl["b"])], 1), (vmap[str(cl["a"])], -1)], int(cl["delta"])))
            elif op == "anchor":
                col = vmap[str(cl["var"])]
                val = int(cl["value"])
                var_lo[col] = max(var_lo[col], val)
                var_hi[col] = min(var_hi[col], val)
                eq_rows.append(([(col, 1)], val))
            elif op == "window":
                col = vmap[str(cl["var"])]
                var_lo[col] = max(var_lo[col], int(cl["lo"]))
                var_hi[col] = min(var_hi[col], int(cl["hi"]))
            elif op == "precedence":
                gap = int(cl.get("min_gap", 0))
                ca, cb = vmap[str(cl["a"])], vmap[str(cl["b"])]
                ineqs.append(th2.DirectedIntInequality(u=ca, v=cb, a=1, b=gap, c=1, d=0))
            elif op == "modular_clock":
                k_col = len(vmap) + len(aux_bounds)
                M = int(cl["modulus"])
                max_k = (default_hi - default_lo) // max(abs(M), 1) + 2
                aux_bounds.append((-max_k, max_k))
                eq_rows.append(
                    ([(vmap[str(cl["b"])], 1), (vmap[str(cl["a"])], -1), (k_col, -M)], int(cl["delta"]))
                )
            else:
                raise ValueError(f"Unknown temporal_schedule op {op!r}")

        ncols = len(vmap) + len(aux_bounds)
        lo = [var_lo[i] for i in range(len(vmap))] + [b[0] for b in aux_bounds]
        hi = [var_hi[i] for i in range(len(vmap))] + [b[1] for b in aux_bounds]
        A = se.SparseIntMatrix(len(eq_rows), ncols)
        c = [0] * len(eq_rows)
        for r_i, (ents, rhs) in enumerate(eq_rows):
            for col_j, coeff in ents:
                A.add_entry(r_i, col_j, coeff)
            c[r_i] = rhs
        rep = th2.solve_hybrid_torsor_tarski(A, c, lo, hi, ineqs=ineqs, max_branch_nodes=4096)
        return rep, vmap

    all_idx = list(range(len(claims)))
    rep, vmap = build_and_solve_tarski(all_idx)
    if rep.sound_verdict == "CERTIFIED_SAT":
        assert rep.x_feasible is not None
        wit = {name: int(rep.x_feasible[col]) for name, col in vmap.items()}
        for cl in claims:
            op = cl["op"]
            if op == "offset":
                assert wit[str(cl["b"])] - wit[str(cl["a"])] == int(cl["delta"])
            elif op == "anchor":
                assert wit[str(cl["var"])] == int(cl["value"])
            elif op == "window":
                assert int(cl["lo"]) <= wit[str(cl["var"])] <= int(cl["hi"])
            elif op == "precedence":
                assert wit[str(cl["a"])] + int(cl.get("min_gap", 0)) <= wit[str(cl["b"])]
            elif op == "modular_clock":
                assert (wit[str(cl["b"])] - wit[str(cl["a"])] - int(cl["delta"])) % int(cl["modulus"]) == 0
        return ContradictionAutopsy(
            domain="temporal_schedule",
            title=title,
            verdict="CERTIFIED_CONSISTENT",
            total_claims=len(claims),
            certificate={"verified": True, "stage": rep.proof_stage, "branch_nodes": rep.bb_nodes_explored},
            verified_witness=wit,
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )
    if rep.sound_verdict == "OPEN_BUDGET_EXCEEDED":
        return ContradictionAutopsy(
            domain="temporal_schedule",
            title=title,
            verdict="OPEN_BUDGET_EXCEEDED",
            total_claims=len(claims),
            certificate={"branch_nodes": rep.bb_nodes_explored, "stage": rep.proof_stage},
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )

    mus_claims, mcs_repairs = _extract_mus_and_mcs(
        claims, lambda sub: build_and_solve_tarski(sub)[0].sound_verdict == "CERTIFIED_UNSAT"
    )
    return ContradictionAutopsy(
        domain="temporal_schedule",
        title=title,
        verdict="CERTIFIED_CONTRADICTION",
        total_claims=len(claims),
        contradiction_class=rep.proof_stage,
        certificate={
            "verified": True,
            "proof_stage": rep.proof_stage,
            "cg_cuts_added": len(rep.cg_cuts_derived),
            "branch_nodes": rep.bb_nodes_explored,
            "detail": rep.contradiction_reason,
        },
        mus_claims=mus_claims,
        mcs_repairs=mcs_repairs,
        elapsed_ms=(time.perf_counter() - t0) * 1000.0,
    )


# ---------------------------------------------------------------------------
# Domain 2: Exact Unit-Conversion & FX Micro-Arbitrage (`unit_conversion`)
# ---------------------------------------------------------------------------

def _compile_unit_conversion(spec: Dict[str, Any], t0: float) -> ContradictionAutopsy:
    """Compile multiplicative rational claims val[b] = (sign * num / den) * val[a]
    into exact prime-exponent Z-torsors (one per prime p) + Z/2Z sign parity channel!
    ZERO floats, ZERO logarithms — detects 10^-30 micro-arbitrage with 100% exactness!
    """
    title = str(spec.get("title", "Unit Conversion & Ratio Arbitrage Audit"))
    claims: List[Dict[str, Any]] = list(spec.get("claims", []))

    # Pre-factor every claim once (exact integers!)
    parsed: List[Tuple[str, str, int, Dict[int, int]]] = []  # (a, b, sign_bit, prime_exps)
    all_primes: Set[int] = set()
    for cl in claims:
        op = cl.get("op", "ratio")
        if op == "ratio":
            a, b = str(cl["from"]), str(cl["to"])
            num = int(cl["num"])
            den = int(cl.get("den", 1))
        elif op == "anchor_ratio":
            a, b = "__BASE_UNIT_1__", str(cl["unit"])
            num = int(cl["num"])
            den = int(cl.get("den", 1))
        else:
            raise ValueError(f"Unknown unit_conversion op {op!r}")
        if num == 0 or den == 0:
            raise ValueError("Zero ratio not permitted in multiplicative unit_conversion")
        sgn = -1 if ((num < 0) ^ (den < 0)) else 1
        if "sign" in cl and int(cl["sign"]) < 0:
            sgn = -sgn
        sign_bit = 1 if sgn < 0 else 0
        exps = _prime_factors_signed(abs(num), abs(den))
        all_primes.update(exps.keys())
        parsed.append((a, b, sign_bit, exps))

    sorted_primes = sorted(all_primes)

    def solve_subset(sub_idx: Sequence[int], want_w: bool = False):
        units: Dict[str, int] = {}
        for i in sub_idx:
            a, b, _, _ = parsed[i]
            units.setdefault(a, len(units))
            units.setdefault(b, len(units))
        n_u = len(units)
        m = len(sub_idx)

        # 1. Check Z/2Z sign parity channel: s_b - s_a - 2 * k_i = sign_bit
        A_s = se.SparseIntMatrix(m, n_u + m)
        c_s = [0] * m
        for r_i, idx in enumerate(sub_idx):
            a, b, sbit, _ = parsed[idx]
            A_s.add_entry(r_i, units[b], 1)
            A_s.add_entry(r_i, units[a], -1)
            A_s.add_entry(r_i, n_u + r_i, -2)
            c_s[r_i] = sbit
        res_s = se.solve_torsor(A_s, c_s, ring="Z", want_witness=want_w)
        if res_s.status != "SAT_INTEGRAL":
            msg_c = res_s.status
            if want_w:
                ok_c, msg_c = se.verify_torsor_certificate(A_s, c_s, res_s)
                assert ok_c, msg_c
            return False, "UNIT_SIGN_PARITY_TORSION", {"channel": "sign_mod_2", "detail": msg_c}, None

        # 2. Check each prime exponent channel p: e_b^(p) - e_a^(p) = v_p(num / den) over Z!
        prime_witnesses: Dict[int, List[int]] = {}
        for p in sorted_primes:
            A_p = se.SparseIntMatrix(m, n_u)
            c_p = [0] * m
            for r_i, idx in enumerate(sub_idx):
                a, b, _, exps = parsed[idx]
                A_p.add_entry(r_i, units[b], 1)
                A_p.add_entry(r_i, units[a], -1)
                c_p[r_i] = exps.get(p, 0)
            res_p = se.solve_torsor(A_p, c_p, ring="Z", want_witness=want_w)
            if res_p.status != "SAT_INTEGRAL":
                msg_c = res_p.status
                if want_w:
                    ok_c, msg_c = se.verify_torsor_certificate(A_p, c_p, res_p)
                    assert ok_c, msg_c
                cert = {
                    "channel": f"prime_exponent_p={p}",
                    "prime": p,
                    "status": res_p.status,
                    "detail": msg_c,
                }
                if res_p.dual_free_witness is not None:
                    cert["dual_cycle_weight"] = int(
                        sum(w * c_p[r] for r, w in res_p.dual_free_witness.items())
                    )
                return False, "UNSAT_UNIT_ARBITRAGE_PRIME_COHOMOLOGY", cert, None
            if want_w:
                assert res_p.x_int is not None
                prime_witnesses[p] = list(res_p.x_int)

        if not want_w:
            return True, "SAT_INTEGRAL", {}, None

        # Reconstruct exact rational values for every unit relative to witness exponents!
        assert res_s.x_int is not None
        wit_units: Dict[str, str] = {}
        for uname, ucol in units.items():
            if uname == "__BASE_UNIT_1__":
                continue
            sgn_str = "-" if (res_s.x_int[ucol] & 1) else ""
            num_u = 1
            den_u = 1
            for p, wvec in prime_witnesses.items():
                ep = wvec[ucol]
                if ep > 0:
                    num_u *= p ** ep
                elif ep < 0:
                    den_u *= p ** (-ep)
            wit_units[uname] = f"{sgn_str}{num_u}/{den_u}" if den_u != 1 else f"{sgn_str}{num_u}"

        # Independent exact integer cross-multiplication verification on EVERY claim!
        for idx in sub_idx:
            a, b, sbit, exps = parsed[idx]
            ua, ub = units[a], units[b]
            assert ((res_s.x_int[ub] - res_s.x_int[ua]) & 1) == sbit
            for p in sorted_primes:
                assert prime_witnesses[p][ub] - prime_witnesses[p][ua] == exps.get(p, 0)

        return True, "SAT_INTEGRAL", {"primes_checked": len(sorted_primes), "sign_channel": "Z/2Z"}, wit_units

    all_idx = list(range(len(claims)))
    ok, cls, cert, wit = solve_subset(all_idx, want_w=True)
    if ok:
        return ContradictionAutopsy(
            domain="unit_conversion",
            title=title,
            verdict="CERTIFIED_CONSISTENT",
            total_claims=len(claims),
            certificate=cert,
            verified_witness=wit,
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )

    mus_claims, mcs_repairs = _extract_mus_and_mcs(
        claims, lambda sub: not solve_subset(sub, want_w=False)[0]
    )
    return ContradictionAutopsy(
        domain="unit_conversion",
        title=title,
        verdict="CERTIFIED_CONTRADICTION",
        total_claims=len(claims),
        contradiction_class=cls,
        certificate=cert,
        mus_claims=mus_claims,
        mcs_repairs=mcs_repairs,
        elapsed_ms=(time.perf_counter() - t0) * 1000.0,
    )


# ---------------------------------------------------------------------------
# Domain 3: Conservation & Double-Entry Flow Ledgers (`conservation_ledger`)
# ---------------------------------------------------------------------------

def _compile_conservation_ledger(spec: Dict[str, Any], t0: float) -> ContradictionAutopsy:
    """Compile 0-cell Kirchhoff balance equations, 1-cell potential transfers, and
    2-cell triadic H^2 clearing constraints (delta^1 y = d) over Z!
    """
    title = str(spec.get("title", "Conservation & Ledger Audit"))
    claims: List[Dict[str, Any]] = list(spec.get("claims", []))

    def build_and_solve(sub_idx: Sequence[int], want_w: bool = False):
        sub_cl = [claims[i] for i in sub_idx]
        # Unified exact Z linear variable namespace:
        #   - "pot:<acct>" for 0-cell account potentials
        #   - "flow:<edge>" for 1-cell flow variables
        #   - "tri_edge:<a|b>" for oriented 1-cochain edge variables in H^2 triadic audits!
        vmap: Dict[str, int] = {}
        rows_data: List[Tuple[List[Tuple[int, int]], int]] = []
        for cl in sub_cl:
            op = cl.get("op")
            if op == "potential_diff":
                ca = vmap.setdefault(f"pot:{cl['from']}", len(vmap))
                cb = vmap.setdefault(f"pot:{cl['to']}", len(vmap))
                rows_data.append(([(cb, 1), (ca, -1)], int(cl["amount"])))
            elif op == "account_anchor":
                ca = vmap.setdefault(f"pot:{cl['account']}", len(vmap))
                rows_data.append(([(ca, 1)], int(cl["balance"])))
            elif op == "flow_conservation":
                # sum_k coeff_k * flow[var_k] = net_injection
                ents: List[Tuple[int, int]] = []
                for term in cl["terms"]:
                    cf = vmap.setdefault(f"flow:{term['edge']}", len(vmap))
                    ents.append((cf, int(term["coeff"])))
                rows_data.append((ents, int(cl["net"])))
            elif op == "triadic_audit":
                # Oriented 2-simplex coboundary: delta^1 y (u, v, w) = rhs
                u, v, w = str(cl["u"]), str(cl["v"]), str(cl["w"])
                verts = [u, v, w]
                inv = sum(1 for i in range(3) for j in range(i + 1, 3) if verts[i] > verts[j])
                orient = -1 if (inv & 1) else 1
                a, b, c_v = sorted(verts)
                ents = []
                for (p1, p2), sgn in (((b, c_v), orient), ((a, c_v), -orient), ((a, b), orient)):
                    ce = vmap.setdefault(f"edge:{p1}->{p2}", len(vmap))
                    ents.append((ce, sgn))
                rows_data.append((ents, int(cl["rhs"])))
            else:
                raise ValueError(f"Unknown conservation_ledger op {op!r}")

        A = se.SparseIntMatrix(len(rows_data), len(vmap))
        c_vec = [0] * len(rows_data)
        for r_i, (ents, rhs) in enumerate(rows_data):
            for col_j, val in ents:
                A.add_entry(r_i, col_j, val)
            c_vec[r_i] = rhs
        res = se.solve_torsor(A, c_vec, ring="Z", want_witness=want_w)
        return A, c_vec, res, vmap

    all_idx = list(range(len(claims)))
    A, c_vec, res, vmap = build_and_solve(all_idx, want_w=True)
    ok_cert, cert_msg = se.verify_torsor_certificate(A, c_vec, res)
    assert ok_cert, f"Internal certificate failure: {cert_msg}"

    if res.status == "SAT_INTEGRAL":
        assert res.x_int is not None
        wit = {name: int(res.x_int[col]) for name, col in vmap.items()}
        return ContradictionAutopsy(
            domain="conservation_ledger",
            title=title,
            verdict="CERTIFIED_CONSISTENT",
            total_claims=len(claims),
            certificate={"verified": True, "detail": cert_msg},
            verified_witness=wit,
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )

    mus_claims, mcs_repairs = _extract_mus_and_mcs(
        claims, lambda sub: build_and_solve(sub, want_w=False)[2].status != "SAT_INTEGRAL"
    )
    cert_d: Dict[str, Any] = {"verified": True, "detail": cert_msg}
    if res.torsion_cert is not None:
        cert_d["torsion_mod"] = int(res.torsion_cert[0])
        cert_d["torsion_rem"] = int(res.torsion_cert[1])
    if res.dual_free_witness is not None:
        cert_d["dual_support_size"] = sum(1 for v in res.dual_free_witness.values() if v != 0)
    return ContradictionAutopsy(
        domain="conservation_ledger",
        title=title,
        verdict="CERTIFIED_CONTRADICTION",
        total_claims=len(claims),
        contradiction_class=res.status,
        certificate=cert_d,
        mus_claims=mus_claims,
        mcs_repairs=mcs_repairs,
        elapsed_ms=(time.perf_counter() - t0) * 1000.0,
    )


# ---------------------------------------------------------------------------
# Domain 4: Policy & Access-Control Horn/Mutex Rules (`access_policy`)
# ---------------------------------------------------------------------------

def _compile_access_policy(spec: Dict[str, Any], t0: float) -> ContradictionAutopsy:
    """Compile RBAC/ABAC Boolean policy rules into Cycle 6 `tarski_hybrid_v2`
    (Chvatal-Gomory cutting-plane closure + Tarjan equality SCCs + sound budgeted B&B!).
    """
    title = str(spec.get("title", "Access-Control Policy Audit"))
    claims: List[Dict[str, Any]] = list(spec.get("claims", []))
    max_nodes = int(spec.get("max_branch_nodes", 4096))

    def build_and_solve(sub_idx: Sequence[int]):
        sub_cl = [claims[i] for i in sub_idx]
        vmap: Dict[str, int] = {}
        for cl in sub_cl:
            for k in ("var", "from", "to", "then"):
                if k in cl:
                    vmap.setdefault(str(cl[k]), len(vmap))
            for k in ("vars", "if_all"):
                if k in cl:
                    for vname in cl[k]:
                        vmap.setdefault(str(vname), len(vmap))

        n_base = len(vmap)
        lo: List[int] = [0] * n_base
        hi: List[int] = [1] * n_base
        ineqs: List[th2.DirectedIntInequality] = []
        eq_rows: List[Tuple[List[Tuple[int, int]], int]] = []

        for cl in sub_cl:
            op = cl.get("op")
            if op == "require":
                c_v = vmap[str(cl["var"])]
                lo[c_v] = max(lo[c_v], 1)
            elif op == "forbid":
                c_v = vmap[str(cl["var"])]
                hi[c_v] = min(hi[c_v], 0)
            elif op == "implies":
                ineqs.append(th2.DirectedIntInequality(u=vmap[str(cl["from"])], v=vmap[str(cl["to"])]))
            elif op == "horn":
                # (AND_i p_i) -> q  <==>  sum(p_i) - q <= k - 1
                # Encoded cleanly via slack s in [0, k]: sum(p_i) - q + s = k - 1!
                prems = [vmap[str(v)] for v in cl["if_all"]]
                concl = vmap[str(cl["then"])]
                k = len(prems)
                s_col = len(lo)
                lo.append(0)
                hi.append(k)
                ents = [(p_c, 1) for p_c in prems] + [(concl, -1), (s_col, 1)]
                eq_rows.append((ents, k - 1))
            elif op in ("mutex", "at_most_one"):
                # sum(x_i) <= 1  <==>  sum(x_i) + s = 1 with s in [0, 1]!
                vs = [vmap[str(v)] for v in cl["vars"]]
                s_col = len(lo)
                lo.append(0)
                hi.append(1)
                ents = [(c_i, 1) for c_i in vs] + [(s_col, 1)]
                eq_rows.append((ents, 1))
            elif op == "exactly_one":
                vs = [vmap[str(v)] for v in cl["vars"]]
                eq_rows.append(([(c_i, 1) for c_i in vs], 1))
            elif op == "cardinality":
                vs = [vmap[str(v)] for v in cl["vars"]]
                if "eq" in cl:
                    eq_rows.append(([(c_i, 1) for c_i in vs], int(cl["eq"])))
                else:
                    min_k = int(cl.get("min", 0))
                    max_k = int(cl.get("max", len(vs)))
                    # sum(vs) - t = min_k with t in [0, max_k - min_k]
                    if max_k < min_k:
                        # Direct impossible cardinality
                        s_col = len(lo)
                        lo.append(1)
                        hi.append(0)
                    else:
                        t_col = len(lo)
                        lo.append(0)
                        hi.append(max_k - min_k)
                        eq_rows.append(([(c_i, 1) for c_i in vs] + [(t_col, -1)], min_k))
            else:
                raise ValueError(f"Unknown access_policy op {op!r}")

        A = se.SparseIntMatrix(len(eq_rows), len(lo))
        c_vec = [0] * len(eq_rows)
        for r_i, (ents, rhs) in enumerate(eq_rows):
            for col_j, val in ents:
                A.add_entry(r_i, col_j, val)
            c_vec[r_i] = rhs
        rep = th2.solve_hybrid_torsor_tarski(A, c_vec, lo, hi, ineqs=ineqs, max_branch_nodes=max_nodes)
        return rep, vmap

    all_idx = list(range(len(claims)))
    rep, vmap = build_and_solve(all_idx)

    if rep.sound_verdict == "CERTIFIED_SAT":
        assert rep.x_feasible is not None
        wit = {name: int(rep.x_feasible[col]) for name, col in vmap.items()}
        # Independent claim-by-claim policy verification!
        for cl in claims:
            op = cl["op"]
            if op == "require":
                assert wit[str(cl["var"])] == 1
            elif op == "forbid":
                assert wit[str(cl["var"])] == 0
            elif op == "implies":
                assert wit[str(cl["from"])] <= wit[str(cl["to"])]
            elif op == "horn":
                if all(wit[str(v)] == 1 for v in cl["if_all"]):
                    assert wit[str(cl["then"])] == 1
            elif op in ("mutex", "at_most_one"):
                assert sum(wit[str(v)] for v in cl["vars"]) <= 1
            elif op == "exactly_one":
                assert sum(wit[str(v)] for v in cl["vars"]) == 1
            elif op == "cardinality":
                tot = sum(wit[str(v)] for v in cl["vars"])
                if "eq" in cl:
                    assert tot == int(cl["eq"])
                else:
                    assert int(cl.get("min", 0)) <= tot <= int(cl.get("max", len(cl["vars"])))
        return ContradictionAutopsy(
            domain="access_policy",
            title=title,
            verdict="CERTIFIED_CONSISTENT",
            total_claims=len(claims),
            certificate={"verified": True, "stage": rep.proof_stage, "branch_nodes": rep.bb_nodes_explored},
            verified_witness=wit,
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )

    if rep.sound_verdict == "OPEN_BUDGET_EXCEEDED":
        return ContradictionAutopsy(
            domain="access_policy",
            title=title,
            verdict="OPEN_BUDGET_EXCEEDED",
            total_claims=len(claims),
            certificate={"branch_nodes": rep.bb_nodes_explored, "stage": rep.proof_stage},
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )

    mus_claims, mcs_repairs = _extract_mus_and_mcs(
        claims, lambda sub: build_and_solve(sub)[0].sound_verdict == "CERTIFIED_UNSAT"
    )
    return ContradictionAutopsy(
        domain="access_policy",
        title=title,
        verdict="CERTIFIED_CONTRADICTION",
        total_claims=len(claims),
        contradiction_class=rep.proof_stage,
        certificate={
            "verified": True,
            "proof_stage": rep.proof_stage,
            "cg_cuts_added": len(rep.cg_cuts_derived),
            "branch_nodes": rep.bb_nodes_explored,
            "detail": rep.contradiction_reason,
        },
        mus_claims=mus_claims,
        mcs_repairs=mcs_repairs,
        elapsed_ms=(time.perf_counter() - t0) * 1000.0,
    )


# ---------------------------------------------------------------------------
# Domain 5: Discrete Equivalence, Negation & Group Labeling (`group_labeling`)
# ---------------------------------------------------------------------------

def _compile_group_labeling(spec: Dict[str, Any], t0: float) -> ContradictionAutopsy:
    """Compile equivalence (`same`), negation (`negate`), modular offsets/flips
    (`mod_offset`, `mod_negate`), integer scales, and pins over Z / Z_m!
    """
    title = str(spec.get("title", "Discrete Group Labeling Audit"))
    claims: List[Dict[str, Any]] = list(spec.get("claims", []))
    default_mod: Optional[int] = int(spec["modulus"]) if "modulus" in spec and spec["modulus"] is not None else None

    def build_and_solve(sub_idx: Sequence[int], want_w: bool = False):
        sub_cl = [claims[i] for i in sub_idx]
        vmap: Dict[str, int] = {}
        for cl in sub_cl:
            for k in ("a", "b", "var"):
                if k in cl:
                    vmap.setdefault(str(cl[k]), len(vmap))
        wrap_cols: Dict[int, int] = {}
        n_extra = 0
        for r_i, cl in enumerate(sub_cl):
            m_val = cl.get("modulus", default_mod)
            op = cl.get("op")
            if op in ("different", "mod_offset", "mod_negate") or (
                m_val is not None and op in ("same", "negate")
            ):
                wrap_cols[r_i] = len(vmap) + n_extra
                n_extra += 1
        A = se.SparseIntMatrix(len(sub_cl), len(vmap) + n_extra)
        c_vec = [0] * len(sub_cl)

        for r_i, cl in enumerate(sub_cl):
            op = cl.get("op")
            m_val = cl.get("modulus", default_mod)
            if op == "same":
                A.add_entry(r_i, vmap[str(cl["b"])], 1)
                A.add_entry(r_i, vmap[str(cl["a"])], -1)
                if r_i in wrap_cols:
                    A.add_entry(r_i, wrap_cols[r_i], -int(m_val))
                c_vec[r_i] = 0
            elif op == "negate":
                # x[b] + x[a] = offset (or mod M)
                A.add_entry(r_i, vmap[str(cl["b"])], 1)
                A.add_entry(r_i, vmap[str(cl["a"])], 1)
                if r_i in wrap_cols:
                    A.add_entry(r_i, wrap_cols[r_i], -int(m_val))
                c_vec[r_i] = int(cl.get("offset", 0))
            elif op == "different":
                # Over Z/2Z (or given modulus): x[b] - x[a] == 1 (mod M)
                mod_eff = int(m_val) if m_val is not None else 2
                if r_i not in wrap_cols:
                    wrap_cols[r_i] = A.ncols
                    A.ncols += 1
                A.add_entry(r_i, vmap[str(cl["b"])], 1)
                A.add_entry(r_i, vmap[str(cl["a"])], -1)
                A.add_entry(r_i, wrap_cols[r_i], -mod_eff)
                c_vec[r_i] = int(cl.get("delta", 1))
            elif op == "mod_offset":
                mod_eff = int(cl.get("modulus", default_mod or 2))
                A.add_entry(r_i, vmap[str(cl["b"])], 1)
                A.add_entry(r_i, vmap[str(cl["a"])], -1)
                A.add_entry(r_i, wrap_cols[r_i], -mod_eff)
                c_vec[r_i] = int(cl["delta"])
            elif op == "mod_negate":
                mod_eff = int(cl.get("modulus", default_mod or 2))
                A.add_entry(r_i, vmap[str(cl["b"])], 1)
                A.add_entry(r_i, vmap[str(cl["a"])], 1)
                A.add_entry(r_i, wrap_cols[r_i], -mod_eff)
                c_vec[r_i] = int(cl.get("delta", 0))
            elif op == "scale_relation":
                A.add_entry(r_i, vmap[str(cl["b"])], int(cl["coeff_b"]))
                A.add_entry(r_i, vmap[str(cl["a"])], -int(cl["coeff_a"]))
                c_vec[r_i] = int(cl.get("rhs", 0))
            elif op == "pin":
                A.add_entry(r_i, vmap[str(cl["var"])], 1)
                c_vec[r_i] = int(cl["value"])
            else:
                raise ValueError(f"Unknown group_labeling op {op!r}")

        res = se.solve_torsor(A, c_vec, ring="Z", want_witness=want_w)
        return A, c_vec, res, vmap

    all_idx = list(range(len(claims)))
    A, c_vec, res, vmap = build_and_solve(all_idx, want_w=True)
    ok_cert, cert_msg = se.verify_torsor_certificate(A, c_vec, res)
    assert ok_cert, f"Internal certificate failure: {cert_msg}"

    if res.status == "SAT_INTEGRAL":
        assert res.x_int is not None
        wit = {name: int(res.x_int[col]) for name, col in vmap.items()}
        return ContradictionAutopsy(
            domain="group_labeling",
            title=title,
            verdict="CERTIFIED_CONSISTENT",
            total_claims=len(claims),
            certificate={"verified": True, "detail": cert_msg},
            verified_witness=wit,
            elapsed_ms=(time.perf_counter() - t0) * 1000.0,
        )

    mus_claims, mcs_repairs = _extract_mus_and_mcs(
        claims, lambda sub: build_and_solve(sub, want_w=False)[2].status != "SAT_INTEGRAL"
    )
    cert_d: Dict[str, Any] = {"verified": True, "detail": cert_msg}
    if res.torsion_cert is not None:
        cert_d["torsion_mod"] = int(res.torsion_cert[0])
        cert_d["torsion_rem"] = int(res.torsion_cert[1])
    if res.dual_free_witness is not None:
        cert_d["dual_support_size"] = sum(1 for v in res.dual_free_witness.values() if v != 0)
    return ContradictionAutopsy(
        domain="group_labeling",
        title=title,
        verdict="CERTIFIED_CONTRADICTION",
        total_claims=len(claims),
        contradiction_class=res.status,
        certificate=cert_d,
        mus_claims=mus_claims,
        mcs_repairs=mcs_repairs,
        elapsed_ms=(time.perf_counter() - t0) * 1000.0,
    )


# ---------------------------------------------------------------------------
# Public Compiler Entrypoints
# ---------------------------------------------------------------------------

SUPPORTED_DOMAINS = (
    "temporal_schedule",
    "unit_conversion",
    "conservation_ledger",
    "access_policy",
    "group_labeling",
)


def compile_and_verify(spec: Dict[str, Any]) -> ContradictionAutopsy:
    """Compile and zero-trust verify a structured claim specification dictionary."""
    t0 = time.perf_counter()
    domain = str(spec.get("domain", ""))
    if domain == "temporal_schedule":
        return _compile_temporal_schedule(spec, t0)
    if domain == "unit_conversion":
        return _compile_unit_conversion(spec, t0)
    if domain == "conservation_ledger":
        return _compile_conservation_ledger(spec, t0)
    if domain == "access_policy":
        return _compile_access_policy(spec, t0)
    if domain == "group_labeling":
        return _compile_group_labeling(spec, t0)
    raise ValueError(f"Unsupported domain {domain!r}; expected one of {SUPPORTED_DOMAINS}")


def verify_json_file(path: Path) -> ContradictionAutopsy:
    """Load a JSON claim specification from disk and run full forensic verification."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    return compile_and_verify(data)


# ==============================================================================
# SECTION 8: RED-TEAM SOPHIST PARADOX GENERATORS (v1.0 + v2.0)
# ==============================================================================

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


# ==============================================================================
# SECTION 9: STANDALONE v2.0.0 ZERO-TRUST VERIFICATION SUITE (8 FLAGSHIP DEMOS)
# ==============================================================================


def run_standalone_v2_verification() -> None:
    t_all = time.perf_counter()
    print("=" * 82)
    print(f"SHEAF RADAR v{__version__} — STANDALONE ZERO-DEPENDENCY VERIFICATION SUITE")
    print("=" * 82)

    # 1. Scale-Trap Float64 Cliff (N=100)
    sh100 = build_purity_gate_scale_trap_torsor(100)
    A100, c100, _ = sh100.build_coboundary()
    A100_f, c100_f = sh100.build_float64_coboundary()
    svd100 = evaluate_float64_svd_torsor(A100_f, c100_f, atol=1e-12)
    r100 = solve_torsor(A100, c100, ring="Z", want_witness=True)
    ok100, _ = verify_torsor_certificate(A100, c100, r100)
    assert (not svd100.verdict_unsat_atol) and r100.status == "UNSAT_FREE_COHOMOLOGY" and ok100
    print(f"[1/8] Scale-Trap Cliff (N=100): float64 SVD FN (unsat={svd100.verdict_unsat_atol}) vs Exact Z={r100.status} (cert={ok100})")

    # 2. Consistent Non-Dyadic Hilbert d=11 (Zero False Positives)
    sh_h, _ = build_consistent_nondyadic_loop(11, "hilbert", "inverse_holonomy")
    Ah, ch, _ = sh_h.build_coboundary(include_anchors=True)
    Ah_f, ch_f = sh_h.build_float64_coboundary(include_anchors=True)
    svd_h = evaluate_float64_svd_torsor(Ah_f, ch_f, atol=1e-12)
    rh = solve_torsor(Ah, ch, ring="Q", want_witness=True)
    ok_h, _ = verify_torsor_certificate(Ah, ch, rh)
    assert svd_h.verdict_unsat_atol and rh.status == "SAT_Q" and ok_h
    print(f"[2/8] Non-Dyadic Hilbert d=11: float64 SVD FP (unsat={svd_h.verdict_unsat_atol}) vs Exact Q={rh.status} (cert={ok_h})")

    # 3. Simplicial RP^2 H^2 Torsion & Exact 10-Face MUS
    rp2 = build_rp2_hemi_icosahedron(defect=1)
    coh_rp2 = rp2.compute_cohomology("Z")
    r_rp2, D1_rp2, d_rp2 = rp2.solve_h2_torsor("Z", want_witness=True)
    mus_rp2 = localize_2complex_h2_mus(rp2, ring="Z", verify_minimality=True)
    assert coh_rp2.format_h2() == "Z/2Z" and r_rp2.status == "UNSAT_TORSION" and len(mus_rp2.mus_ids) == 10
    print(f"[3/8] RP^2 H^2 Torsion: H^1={coh_rp2.format_h1()}, H^2={coh_rp2.format_h2()}, cert={r_rp2.torsion_cert}, MUS={len(mus_rp2.mus_ids)} faces")

    # 4. Decoy Maze l_2 Smearing vs l_0 QuickXplain
    sh_m, culprits, fault_eid = build_shared_edge_decoy_maze(6, 100, seed=20261119)
    cmp_m = evaluate_l2_smearing_vs_quickxplain(sh_m, culprits)
    assert cmp_m.l0_verified_minimal and cmp_m.l0_false_blame_pct == 0.0 and cmp_m.l2_top_k_precision <= 0.6
    print(f"[4/8] Decoy Maze Localization: l_2 top-k={cmp_m.l2_top_k_precision:.2f} vs l_0 QuickXplain false_blame={cmp_m.l0_false_blame_pct:.1f}%")

    # 5. Cycle 5: Unpeelable 3-Regular Tseitin Z/6Z Expander (0% Peel) + Moore Space M(Z/12Z, 1)
    B60, c60, _ = build_unpeelable_tseitin_expander(N=60, modulus=6, defect=1, seed=20261119)
    r60 = solve_torsor(B60, c60, ring="Z", want_witness=True)
    ok60, _ = verify_torsor_certificate(B60, c60, r60)
    m12 = build_simplicial_moore_space(12, defect=1)
    cm12 = m12.compute_cohomology("Z")
    assert r60.peeled_rank == 0 and r60.status == "UNSAT_TORSION" and ok60 and cm12.format_h2() == "Z/12Z"
    print(f"[5/8] Unpeelable Expander N=60 (0% peel): |D1|={r60.single_det_D1_bits}b -> G={r60.double_det_G} "
          f"({r60.double_det_G.bit_length()}b) | Moore M(Z/12Z,1) H^2={cm12.format_h2()}")

    # 6. Cycle 6: Quantum Contextuality (3-Pentagon KCBS CG Ghost) + High-Nullity Hidden CG + Sound Budget
    Ak, ck, lok, hik = build_coupled_kcbs_pentagon_cg_ghost()
    rk = solve_hybrid_torsor_tarski(Ak, ck, lok, hik)
    Ahn, chn, lohn, hihn = build_high_nullity_hidden_cg_cut(extra_free_vars=60, seed=20261119)
    rhn = solve_hybrid_torsor_tarski(Ahn, chn, lohn, hihn)
    Aop, cop, loop, hiop = build_high_nullity_planted_hard_open(n_vars=64, n_eqs=12, seed=20261119)
    rop = solve_hybrid_torsor_tarski(Aop, cop, loop, hiop, max_branch_nodes=2)
    assert rk.sound_verdict == "CERTIFIED_UNSAT" and rk.bb_nodes_explored == 0
    assert rhn.sound_verdict == "CERTIFIED_UNSAT" and rhn.bb_nodes_explored == 0
    assert rop.sound_verdict == "OPEN_BUDGET_EXCEEDED"
    print(f"[6/8] Contextuality & CG Cuts: KCBS={rk.proof_stage} (0 br, {rk.elapsed_ms:.2f}ms) | "
          f"Hidden nu=56={rhn.proof_stage} (0 br, {rhn.elapsed_ms:.2f}ms) | Tight budget={rop.sound_verdict}")

    # 7. Cycle 7: Streaming Pre-Commit Sheaf Firewall (120-Hop Z_2 Liar Flip + Rollback + Batch Audit)
    fw = IncrementalSheafFirewall(ring="Z")
    for i in range(120):
        assert fw.commit_claim(FirewallClaim(i + 1, "affine_1d", {"u": i, "v": i + 1, "coeff_u": -1, "coeff_v": 1, "rhs": 0})).accepted
    v_liar = fw.commit_claim(FirewallClaim(121, "affine_1d", {"u": 0, "v": 120, "coeff_u": -1, "coeff_v": 1, "rhs": 1}))
    ok_batch, _ = fw.verify_committed_state_from_scratch()
    assert (not v_liar.accepted) and v_liar.torsion_cert == (2, 1) and len(v_liar.mus_claim_ids or []) == 121 and ok_batch
    print(f"[7/8] Streaming Firewall: 120-hop Liar rejected in {v_liar.latency_us:.2f} us (cert={v_liar.torsion_cert}, MUS=121, batch_audit={ok_batch})")

    # 8. Cycle 8: 5-Domain Forensic Claim Compiler (10^-21 Unit Micro-Arbitrage Loop)
    aut = compile_and_verify({
        "domain": "unit_conversion",
        "title": "Standalone FX 10^-21 Micro-Arbitrage Loop",
        "claims": [
            {"id": "fx1", "op": "ratio", "from": "USD", "to": "EUR", "num": 92, "den": 100},
            {"id": "fx2", "op": "ratio", "from": "EUR", "to": "GBP", "num": 85, "den": 100},
            {"id": "fx3", "op": "ratio", "from": "GBP", "to": "USD", "num": 500000000000000000001, "den": 391000000000000000000},
        ],
    })
    assert aut.verdict == "CERTIFIED_CONTRADICTION" and len(aut.mus_claims) == 3
    print(f"[8/8] Claim Compiler (Unit Micro-Arbitrage): {aut.verdict} ({aut.contradiction_class}, MUS={len(aut.mus_claims)}, {aut.elapsed_ms:.2f}ms)")

    total_ms = (time.perf_counter() - t_all) * 1000.0
    print("=" * 82)
    print(f"ALL 8 STANDALONE v{__version__} CHECKS PASSED (ZERO-TRUST CERTIFIED) IN {total_ms:.1f} ms!")
    print("=" * 82)


if __name__ == "__main__":
    run_standalone_v2_verification()

