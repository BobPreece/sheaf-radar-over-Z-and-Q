"""Pure-Stdlib IEEE-754 float64 Baseline Simulator.

Implements:
1. Symmetric eigensolver (Householder tridiagonalization + implicit Wilkinson QL/QR)
   for the homogeneous sheaf Laplacian L_0 = (delta^0)^T delta^0.
2. Direct Golub-Kahan-Reinsch bidiagonalization + implicit QR SVD for delta^0
   (without squaring condition numbers via A^T A), plus exact SVD least-squares
   residual evaluation under both SIGMA (atol=1e-12) and standard numerical rank
   (max(m,n) * eps * sigma_max) cutoffs.
3. Pure-stdlib Jacobi-preconditioned Conjugate Gradient (CG) and SVD least-squares
   solver for l_2 Hodge harmonic energy and Kirchhoff edge blame distribution.

Strictly Python 3 standard library only (math, dataclasses, typing).
"""

from dataclasses import dataclass
import math
from typing import Dict, List, Optional, Sequence, Tuple

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
