"""Exact Z/Q Sparse Linear Algebra v2.0:
- DHSW +/-1 unit-pivot, degree-1 leaf & O(E log V) degree-2 contraction
- 61-bit multi-prime CRT exact sparse determinant & Cramer rational lifting
- Pernet-Stein / Storjohann Double-Determinant lattice compression G = gcd(D_1, D_2)
- Prime-power local sparse Digit-SNF decomposition (arXiv:2511.00677)
- Sparse q-adic local torsion refutation with dual witness replay + Bezout witness lifting
- Guardrail A exact pivot-basis Bareiss + Mod-D Column-HNF + Iliopoulos Mod-2D SNF fallback
- Guardrail B strict Q row-LCM vs Z unscaled separation.

Strictly Python 3 standard library only. Zero fractions.Fraction usage.
"""

from collections import deque
from dataclasses import dataclass, field
import math
import random
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

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
