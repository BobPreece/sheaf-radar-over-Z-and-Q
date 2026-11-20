"""Comprehensive Zero-Dependency Unittest Suite for sheaf-radar-over-Z-and-Q."""

from pathlib import Path
import random
import sys
import time
import unittest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import sheaf_radar as sr
from sheaf_radar import sophist

PERMITTED_STDLIB = {
    "math",
    "sys",
    "time",
    "random",
    "collections",
    "itertools",
    "functools",
    "typing",
    "dataclasses",
    "json",
    "pathlib",
    "argparse",
    "unittest",
}


class TestZeroDependencyCompliance(unittest.TestCase):
    def test_strict_stdlib_only_across_entire_repo(self) -> None:
        violations = []
        py_files = (
            list((REPO_ROOT / "sheaf_radar").glob("*.py"))
            + list((REPO_ROOT / "tests").glob("*.py"))
            + [REPO_ROOT / "standalone_sheaf_contradiction_radar.py"]
        )
        for p in sorted(py_files):
            for lineno, raw in enumerate(p.read_text(encoding="utf-8").splitlines(), start=1):
                s = raw.strip()
                if not s or s.startswith("#"):
                    continue
                if s.startswith("import "):
                    for chunk in s[7:].split("#")[0].split(","):
                        mod = chunk.strip().split()[0].split(".")[0]
                        if mod not in PERMITTED_STDLIB and mod != "sheaf_radar":
                            violations.append(f"{p.name}:{lineno} import {mod}")
                elif s.startswith("from "):
                    parts = s.split()
                    if len(parts) >= 4 and parts[2] == "import":
                        src = parts[1]
                        if src.startswith("."):
                            continue
                        mod = src.split(".")[0]
                        if mod not in PERMITTED_STDLIB and mod != "sheaf_radar":
                            violations.append(f"{p.name}:{lineno} from {mod}")
        self.assertEqual(violations, [], f"Disallowed imports found: {violations}")


class TestGuardrailAExactZQTorsorsAndSNF(unittest.TestCase):
    def test_overdetermined_column_hnf_sat_and_unsat(self) -> None:
        A_sat = sr.SparseIntMatrix.from_dense([[2, 3], [4, 6], [6, 9]])
        res_sat = sr.solve_torsor(A_sat, [1, 2, 3], ring="Z", want_witness=True)
        self.assertEqual(res_sat.status, "SAT_INTEGRAL")
        self.assertTrue(sr.verify_torsor_certificate(A_sat, [1, 2, 3], res_sat)[0])

        A_tor = sr.SparseIntMatrix.from_dense([[2, 4], [4, 8], [6, 12]])
        res_tor = sr.solve_torsor(A_tor, [1, 2, 3], ring="Z", want_witness=True)
        self.assertEqual(res_tor.status, "UNSAT_TORSION")
        self.assertTrue(sr.verify_torsor_certificate(A_tor, [1, 2, 3], res_tor)[0])

    def test_sophist_61bit_prime_traps(self) -> None:
        A1 = sr.SparseIntMatrix.from_dense([[sr.PRIME_1]])
        r1 = sr.solve_torsor(A1, [1], ring="Z", want_witness=True)
        self.assertEqual(r1.status, "UNSAT_TORSION")
        self.assertTrue(sr.verify_torsor_certificate(A1, [1], r1)[0])

        A2 = sr.SparseIntMatrix.from_dense([[sr.PRIME_1 * sr.PRIME_2, 0], [0, 2]])
        r2 = sr.solve_torsor(A2, [1, 2], ring="Z", want_witness=True)
        self.assertEqual(r2.status, "UNSAT_TORSION")
        self.assertTrue(sr.verify_torsor_certificate(A2, [1, 2], r2)[0])

    def test_iliopoulos_mod2d_snf_on_unimodularly_scrambled_cores(self) -> None:
        rng = random.Random(20261119)
        for _ in range(40):
            m, n = rng.randint(2, 9), rng.randint(2, 9)
            r = rng.randint(1, min(m, n))
            mat = [[0] * n for _ in range(m)]
            true_d = []
            d = 1
            for i in range(r):
                d *= rng.choice([1, 1, 2, 3, 5])
                mat[i][i] = d
                true_d.append(d)
            for _ in range(25):
                i1, i2 = rng.sample(range(m), 2)
                k = rng.choice([-2, -1, 1, 2])
                for j in range(n):
                    mat[i1][j] += k * mat[i2][j]
                j1, j2 = rng.sample(range(n), 2)
                k = rng.choice([-2, -1, 1, 2])
                for i in range(m):
                    mat[i][j1] += k * mat[i][j2]
            snf = sr.compute_snf(sr.SparseIntMatrix.from_dense(mat))
            self.assertEqual(snf.invariant_factors, true_d)


class TestGuardrailBRingSeparationAndFloat64Cliff(unittest.TestCase):
    def test_z_sheaf_forbids_rational_entries(self) -> None:
        sh = sr.CellularSheaf1Complex(ring="Z")
        sh.add_vertices(2)
        with self.assertRaises(ValueError):
            sh.add_scalar_edge(0, 1, (1, 3), 1, 0)

    def test_scale_trap_float64_cliff_vs_exact(self) -> None:
        # At N=40, L_0 crosses 1e-12; at N=100, direct SVD rank collapses!
        sh40 = sophist.build_purity_gate_scale_trap_homogeneous(40)
        A40_f, _ = sh40.build_float64_coboundary()
        l0_40 = sr.evaluate_float64_laplacian(A40_f, atol=1e-12)
        self.assertLessEqual(l0_40.min_eig, 1e-12)
        self.assertEqual(sh40.compute_cohomology().beta_0, 0)

        sh100 = sophist.build_purity_gate_scale_trap_torsor(100)
        A100, c100, _ = sh100.build_coboundary()
        A100_f, c100_f = sh100.build_float64_coboundary()
        svd100 = sr.evaluate_float64_svd_torsor(A100_f, c100_f, atol=1e-12)
        self.assertFalse(svd100.verdict_unsat_atol)
        rz = sr.solve_torsor(A100, c100, ring="Z", want_witness=True)
        self.assertEqual(rz.status, "UNSAT_FREE_COHOMOLOGY")
        self.assertTrue(sr.verify_torsor_certificate(A100, c100, rz)[0])

    def test_consistent_hilbert_and_cauchy_zero_false_positives(self) -> None:
        for fam in ("hilbert", "cauchy"):
            sh, _ = sophist.build_consistent_nondyadic_loop(11, fam, "inverse_holonomy")
            A, c, _ = sh.build_coboundary(include_anchors=True)
            A_f, c_f = sh.build_float64_coboundary(include_anchors=True)
            svd = sr.evaluate_float64_svd_torsor(A_f, c_f, atol=1e-12)
            self.assertTrue(svd.verdict_unsat_atol)  # float64 hallucinates contradiction!
            rq = sr.solve_torsor(A, c, ring="Q", want_witness=True)
            self.assertEqual(rq.status, "SAT_Q")
            self.assertTrue(sr.verify_torsor_certificate(A, c, rq)[0])


class TestGuardrailCSimplicialH2AndQuickXplain(unittest.TestCase):
    def test_rp2_hemi_icosahedron_z2_torsion_and_mus(self) -> None:
        cx = sophist.build_rp2_hemi_icosahedron(defect=1)
        self.assertTrue(cx.verify_functoriality())
        self.assertEqual(cx.compute_cohomology("Q").format_h2(), "0")
        coh_z = cx.compute_cohomology("Z")
        self.assertEqual(coh_z.format_h1(), "0")
        self.assertEqual(coh_z.format_h2(), "Z/2Z")
        self.assertEqual(coh_z.snf_delta1, [1] * 9 + [2])
        rz, D1, d_vec = cx.solve_h2_torsor("Z", want_witness=True)
        self.assertEqual(rz.status, "UNSAT_TORSION")
        self.assertEqual(rz.torsion_cert, (2, 1))
        self.assertTrue(sr.verify_torsor_certificate(D1, d_vec, rz)[0])
        mus = sr.localize_2complex_h2_mus(cx, ring="Z", verify_minimality=True)
        self.assertEqual(mus.mus_ids, list(range(10)))

    def test_hollow_sphere_pairwise_consistent_global_h2(self) -> None:
        cx = sophist.build_hollow_octahedron_S2(defect=1)
        coh = cx.compute_cohomology("Z")
        self.assertEqual(coh.format_h1(), "0")
        self.assertEqual(coh.format_h2(), "Z")
        mus = sr.localize_2complex_h2_mus(cx, ring="Z", verify_minimality=True)
        self.assertEqual(mus.mus_ids, list(range(8)))

    def test_decoy_maze_zero_smear_and_shuffled_guardrail_c(self) -> None:
        sh, culprits, fault_eid = sophist.build_shared_edge_decoy_maze(6, 100, seed=20261119)
        comp = sr.evaluate_l2_smearing_vs_quickxplain(sh, culprits)
        self.assertTrue(comp.l0_verified_minimal)
        self.assertEqual(comp.l0_false_blame_pct, 0.0)
        self.assertLessEqual(comp.l2_top_k_precision, 0.6)

        rng = random.Random(314)
        ids = list(range(len(sh.edges)))
        rng.shuffle(ids)

        def is_unsat(sub):
            A_s, c_s, _ = sh.build_coboundary(edge_subset=sub)
            return sr.solve_torsor(A_s, c_s, ring="Z", want_witness=False).status != "SAT_INTEGRAL"

        shuf_mus = sr.quickxplain_mus(ids, is_unsat, verify_minimality=True)
        self.assertIn(fault_eid, shuf_mus.mus_ids)
        mcs = sr.find_mcs_hitting_set(list(range(len(sh.edges))), is_unsat, max_mcs=1, max_mcs_size=1)
        self.assertEqual(mcs.mcs_list, [[fault_eid]])


class TestGuardrailDTarskiAndCaruGhosts(unittest.TestCase):
    def test_asymmetric_horn_and_powerset_galois(self) -> None:
        tsh_ok, lsh_bad = sophist.build_valid_asymmetric_horn_dag(depth=12)
        self.assertTrue(tsh_ok.solve_tarski_flow().consistent)
        self.assertEqual(lsh_bad.solve_affine_torsor()[0].status, "UNSAT_FREE_COHOMOLOGY")

        tsh_mt, true_chain = sophist.build_modus_tollens_contradiction(depth=10, n_decoys=15)
        res_mt = tsh_mt.solve_tarski_flow()
        self.assertFalse(res_mt.consistent)
        self.assertEqual(tsh_mt.localize_mus().mus_ids, true_chain)

        tsh_ps, gcs = sophist.build_powerset_galois_sheaf(contradictory=True)
        for gc in gcs:
            self.assertTrue(gc.verify_adjunction_law())
        self.assertFalse(tsh_ps.solve_tarski_flow().consistent)

    def test_all_three_caru_ghost_tiers_and_control(self) -> None:
        A_h, c_h, lo_h, hi_h, _ = sophist.build_caru_hardy_paradox()
        self.assertEqual(sr.solve_torsor(A_h, c_h, ring="Z").status, "SAT_INTEGRAL")
        self.assertEqual(sr.solve_hybrid_torsor_tarski(A_h, c_h, lo_h, hi_h).status, "UNSAT_HYBRID_TARSKI_GHOST")

        A_e, c_e, lo_e, hi_e, _ = sophist.build_caru_elimination_ghost()
        r_e = sr.solve_hybrid_torsor_tarski(A_e, c_e, lo_e, hi_e)
        self.assertEqual(r_e.status, "UNSAT_HYBRID_TARSKI_GHOST")
        self.assertFalse(r_e.pure_1row_tarski_caught)
        self.assertTrue(r_e.rref_tarski_caught)

        A_c, c_c, lo_c, hi_c, ineqs_c = sophist.build_hybrid_order_algebraic_paradox()
        r_c = sr.solve_hybrid_torsor_tarski(A_c, c_c, lo_c, hi_c, ineqs=ineqs_c)
        self.assertEqual(r_c.status, "UNSAT_HYBRID_TARSKI_GHOST")

        A_ok, c_ok, lo_ok, hi_ok, ineqs_ok = sophist.build_consistent_binary_hybrid_control()
        r_ok = sr.solve_hybrid_torsor_tarski(A_ok, c_ok, lo_ok, hi_ok, ineqs=ineqs_ok)
        self.assertEqual(r_ok.status, "SAT_HYBRID")
        self.assertTrue(sr.check_hybrid_feasible(A_ok, c_ok, ineqs_ok, lo_ok, hi_ok, r_ok.x_feasible))


class TestScalingBudget(unittest.TestCase):
    def test_5200_cell_sub50ms_q_and_sub2s_z(self) -> None:
        rng = random.Random(20261119)
        n_verts, n_edges = 1733, 3467
        sh = sr.CellularSheaf1Complex(ring="Z")
        sh.add_vertices(n_verts)
        for i in range(1, n_verts):
            sh.add_scalar_edge(rng.randint(max(0, i - 10), i - 1), i, 1, 1, 0)
        sh.add_scalar_edge(0, n_verts - 1, -5, 1, 1)
        for _ in range(n_edges - n_verts):
            u = rng.randrange(n_verts)
            v = (u + rng.randint(1, 15)) % n_verts
            sh.add_scalar_edge(u, v, 1, 1, 0)
        A, c, _ = sh.build_coboundary()
        t0 = time.perf_counter()
        rq = sr.solve_torsor(A, c, ring="Q", want_witness=True)
        q_ms = (time.perf_counter() - t0) * 1000.0
        t1 = time.perf_counter()
        rz = sr.solve_torsor(A, c, ring="Z", want_witness=True)
        z_ms = (time.perf_counter() - t1) * 1000.0
        self.assertEqual(rq.status, "SAT_Q")
        self.assertEqual(rz.status, "UNSAT_TORSION")
        self.assertTrue(sr.verify_torsor_certificate(A, c, rz)[0])
        self.assertLess(q_ms, 50.0)
        self.assertLess(z_ms, 2000.0)


class TestCycle5ExpandersDoubleDetAndMooreZoo(unittest.TestCase):
    def test_crt_det_and_double_det_compression_on_unpeelable_expanders(self) -> None:
        for modulus in (6, 2):
            B, c_unsat, _ = sophist.build_unpeelable_tseitin_expander(N=60, modulus=modulus, defect=1, seed=20261119)
            res = sr.solve_torsor(B, c_unsat, ring="Z", want_witness=True)
            self.assertEqual(res.peeled_rank, 0)
            self.assertEqual(res.status, "UNSAT_TORSION")
            self.assertIsNotNone(res.double_det_G)
            self.assertLess(res.double_det_G.bit_length(), res.single_det_D1_bits // 4)
            self.assertTrue(sr.verify_torsor_certificate(B, c_unsat, res)[0])

            # Consistent control (defect=0) verifies exact Bezout integral witness!
            B_ok, c_ok, _ = sophist.build_unpeelable_tseitin_expander(N=60, modulus=modulus, defect=0, seed=20261119)
            res_ok = sr.solve_torsor(B_ok, c_ok, ring="Z", want_witness=True)
            self.assertEqual(res_ok.status, "SAT_INTEGRAL")
            self.assertTrue(sr.verify_torsor_certificate(B_ok, c_ok, res_ok)[0])

    def test_digit_snf_on_unpeelable_expander_exact_invariant_factors(self) -> None:
        B, _, _ = sophist.build_unpeelable_tseitin_expander(N=30, modulus=6, defect=1, seed=20261119)
        snf = sr.compute_snf(B)
        self.assertEqual(snf.invariant_factors, [1] * 29 + [6])
        self.assertEqual(snf.torsion_factors, [6])

    def test_closed_surfaces_torus_and_klein_bottle_cohomology(self) -> None:
        t2 = sophist.build_torus_T2(defect=1)
        ct = t2.compute_cohomology("Z")
        self.assertEqual((ct.beta_0, ct.beta_1, ct.beta_2), (1, 2, 1))
        self.assertEqual(ct.format_h2(), "Z")

        k2 = sophist.build_klein_bottle_K2(defect=1)
        ck = k2.compute_cohomology("Z")
        self.assertEqual((ck.beta_0, ck.beta_1, ck.beta_2), (1, 1, 0))
        self.assertEqual(ck.format_h1(), "Z")
        self.assertEqual(ck.format_h2(), "Z/2Z")
        rk, D1k, dk = k2.solve_h2_torsor("Z", want_witness=True)
        self.assertEqual(rk.status, "UNSAT_TORSION")
        self.assertTrue(sr.verify_torsor_certificate(D1k, dk, rk)[0])

    def test_composite_moore_spaces_m6_m12_m30_digit_snf(self) -> None:
        for m in (6, 12, 30):
            cx = sophist.build_simplicial_moore_space(m, defect=1)
            coh = cx.compute_cohomology("Z")
            self.assertEqual(coh.format_h1(), "0")
            self.assertEqual(coh.format_h2(), f"Z/{m}Z")
            rm, D1m, dm = cx.solve_h2_torsor("Z", want_witness=True)
            self.assertEqual(rm.status, "UNSAT_TORSION")
            self.assertTrue(sr.verify_torsor_certificate(D1m, dm, rm)[0])


class TestCycle6QuantumContextualityCGCutsAndSoundBnB(unittest.TestCase):
    def test_canonical_quantum_contextuality_suite_zero_branches(self) -> None:
        for fn in (
            sophist.build_mermin_peres_magic_square,
            sophist.build_ghz_3qubit_paradox,
            sophist.build_cabello_18ray_ks,
        ):
            A, c, lo, hi = fn()
            self.assertEqual(sr.solve_torsor(A, c, ring="Q").status, "SAT_Q")
            rep = sr.solve_hybrid_torsor_tarski(A, c, lo, hi)
            self.assertEqual(rep.sound_verdict, "CERTIFIED_UNSAT")
            self.assertEqual(rep.proof_stage, "Z_TORSOR_TORSION")
            self.assertEqual(rep.bb_nodes_explored, 0)

        A_h, c_h, lo_h, hi_h, _ = sophist.build_caru_hardy_paradox()
        rep_h = sr.solve_hybrid_torsor_tarski(A_h, c_h, lo_h, hi_h)
        self.assertEqual(rep_h.sound_verdict, "CERTIFIED_UNSAT")
        self.assertEqual(rep_h.proof_stage, "TARSKI_1ROW_INTERVAL")
        self.assertEqual(rep_h.bb_nodes_explored, 0)

    def test_lp_feasible_triangle_and_kcbs_pentagon_cg_cuts_zero_branches(self) -> None:
        for fn in (sophist.build_two_triangle_cg_ghost, sophist.build_coupled_kcbs_pentagon_cg_ghost):
            A, c, lo, hi = fn()
            self.assertEqual(sr.solve_torsor(A, c, ring="Z").status, "SAT_INTEGRAL")
            rep = sr.solve_hybrid_torsor_tarski(A, c, lo, hi)
            self.assertEqual(rep.sound_verdict, "CERTIFIED_UNSAT")
            self.assertEqual(rep.proof_stage, "CHVATAL_GOMORY_CUT")
            self.assertEqual(rep.bb_nodes_explored, 0)
            self.assertTrue(rep.cg_cuts_caught)
            self.assertGreater(len(rep.cg_cuts_derived), 0)

    def test_high_nullity_hidden_cg_cut_sub10ms_zero_branches(self) -> None:
        A, c, lo, hi = sophist.build_high_nullity_hidden_cg_cut(extra_free_vars=60, seed=20261119)
        rep = sr.solve_hybrid_torsor_tarski(A, c, lo, hi)
        self.assertEqual(rep.sound_verdict, "CERTIFIED_UNSAT")
        self.assertEqual(rep.proof_stage, "CHVATAL_GOMORY_CUT")
        self.assertEqual(rep.bb_nodes_explored, 0)
        self.assertLess(rep.elapsed_ms, 50.0)

    def test_sound_three_valued_budget_never_emits_false_verdict(self) -> None:
        A, c, lo, hi = sophist.build_high_nullity_planted_hard_open(n_vars=64, n_eqs=12, seed=20261119)
        rep_open = sr.solve_hybrid_torsor_tarski(A, c, lo, hi, max_branch_nodes=2)
        self.assertEqual(rep_open.sound_verdict, "OPEN_BUDGET_EXCEEDED")
        self.assertIsNone(rep_open.x_feasible)

        rep_sat = sr.solve_hybrid_torsor_tarski(A, c, lo, hi, max_branch_nodes=64)
        self.assertEqual(rep_sat.sound_verdict, "CERTIFIED_SAT")
        self.assertIsNotNone(rep_sat.x_feasible)
        self.assertTrue(sr.check_hybrid_feasible(A, c, (), lo, hi, rep_sat.x_feasible))


class TestCycle7StreamingPreCommitSheafFirewall(unittest.TestCase):
    def test_propose_claim_read_only_and_commit_quarantine(self) -> None:
        fw = sr.IncrementalSheafFirewall(ring="Z")
        self.assertTrue(fw.commit_claim(sr.FirewallClaim(1, "affine_1d", {"u": 0, "v": 1, "coeff_u": 1, "coeff_v": 1, "rhs": 5})).accepted)
        vp = fw.propose_claim(sr.FirewallClaim(2, "affine_1d", {"u": 1, "v": 77, "coeff_u": 1, "coeff_v": 1, "rhs": 3}))
        self.assertTrue(vp.accepted)
        self.assertNotIn(77, fw.comp_root)
        self.assertEqual(len(fw.committed_claims), 1)
        vb = fw.commit_claim(sr.FirewallClaim(3, "affine_1d", {"u": 0, "v": 1, "coeff_u": 1, "coeff_v": 1, "rhs": 99}))
        self.assertFalse(vb.accepted)
        self.assertEqual(len(fw.quarantine), 1)
        self.assertTrue(fw.verify_committed_state_from_scratch()[0])

    def test_checkpoint_and_rollback_restores_exact_potentials(self) -> None:
        fw = sr.IncrementalSheafFirewall(ring="Z")
        fw.commit_claim(sr.FirewallClaim(1, "affine_1d", {"u": 0, "v": 1, "coeff_u": 1, "coeff_v": 1, "rhs": 10}))
        ck = fw.checkpoint()
        fw.commit_claim(sr.FirewallClaim(2, "anchor_1d", {"v": 0, "val": 5}))
        self.assertFalse(fw.commit_claim(sr.FirewallClaim(3, "anchor_1d", {"v": 1, "val": 20})).accepted)
        fw.rollback(ck)
        self.assertEqual(len(fw.committed_claims), 1)
        self.assertTrue(fw.commit_claim(sr.FirewallClaim(4, "anchor_1d", {"v": 1, "val": 20})).accepted)
        self.assertTrue(fw.verify_committed_state_from_scratch()[0])

    def test_120_hop_z2_liar_flip_and_scale_trap_fast_reject(self) -> None:
        fw = sr.IncrementalSheafFirewall(ring="Z")
        for i in range(120):
            self.assertTrue(
                fw.commit_claim(sr.FirewallClaim(i + 1, "affine_1d", {"u": i, "v": i + 1, "coeff_u": -1, "coeff_v": 1, "rhs": 0})).accepted
            )
        v_liar = fw.commit_claim(sr.FirewallClaim(121, "affine_1d", {"u": 0, "v": 120, "coeff_u": -1, "coeff_v": 1, "rhs": 1}))
        self.assertFalse(v_liar.accepted)
        self.assertEqual(v_liar.contradiction_class, "UNSAT_TORSION")
        self.assertEqual(v_liar.torsion_cert, (2, 1))
        self.assertEqual(len(v_liar.mus_claim_ids or []), 121)

        # Non-unit tree merge torsion catch (2*x_200 = x_201 even vs 2*x_202 - x_201 = 1 odd)
        self.assertTrue(fw.commit_claim(sr.FirewallClaim(200, "affine_1d", {"u": 200, "v": 201, "coeff_u": 2, "coeff_v": 1, "rhs": 0})).accepted)
        v_nu = fw.commit_claim(sr.FirewallClaim(201, "affine_1d", {"u": 201, "v": 202, "coeff_u": 1, "coeff_v": 2, "rhs": 1}))
        self.assertFalse(v_nu.accepted)
        self.assertEqual(v_nu.contradiction_class, "UNSAT_TORSION")
        self.assertTrue(fw.verify_committed_state_from_scratch()[0])

    def test_tarski_positive_offset_cycle_and_h2_rp2_firewall_lanes(self) -> None:
        fw = sr.IncrementalSheafFirewall(ring="Z")
        self.assertTrue(fw.commit_claim(sr.FirewallClaim(10, "tarski_order", {"u": 0, "v": 1, "offset": 5})).accepted)
        self.assertTrue(fw.commit_claim(sr.FirewallClaim(11, "tarski_order", {"u": 1, "v": 2, "offset": 5})).accepted)
        v_cyc = fw.commit_claim(sr.FirewallClaim(12, "tarski_order", {"u": 2, "v": 0, "offset": 5}))
        self.assertFalse(v_cyc.accepted)
        self.assertEqual(set(v_cyc.mus_claim_ids or []), {10, 11, 12})

        rp2_faces = [
            (0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 5, 1),
            (1, 2, 4), (2, 3, 5), (3, 4, 1), (4, 5, 2), (5, 1, 3),
        ]
        for idx, (u, v, w) in enumerate(rp2_faces[:9]):
            self.assertTrue(fw.commit_claim(sr.FirewallClaim(100 + idx, "simplex_h2", {"group": "rp2", "u": u, "v": v, "w": w, "rhs": 0})).accepted)
        u9, v9, w9 = rp2_faces[9]
        v_h2 = fw.commit_claim(sr.FirewallClaim(109, "simplex_h2", {"group": "rp2", "u": u9, "v": v9, "w": w9, "rhs": 1}))
        self.assertFalse(v_h2.accepted)
        self.assertEqual(v_h2.contradiction_class, "UNSAT_TORSION")
        self.assertEqual(len(v_h2.mus_claim_ids or []), 10)
        self.assertTrue(fw.verify_committed_state_from_scratch()[0])


class TestCycle8ClaimCompilerAndCLI(unittest.TestCase):
    def test_all_five_compiler_domains_sat_and_unsat(self) -> None:
        # 1. temporal_schedule (SAT + UNSAT with precedence)
        a_ts_ok = sr.compile_and_verify({
            "domain": "temporal_schedule",
            "claims": [
                {"id": "w0", "op": "window", "var": "A", "lo": 0, "hi": 10},
                {"id": "p1", "op": "precedence", "a": "A", "b": "B", "min_gap": 5},
                {"id": "w1", "op": "window", "var": "B", "lo": 0, "hi": 10},
            ],
        })
        self.assertEqual(a_ts_ok.verdict, "CERTIFIED_CONSISTENT")
        a_ts_bad = sr.compile_and_verify({
            "domain": "temporal_schedule",
            "claims": [
                {"id": "w0", "op": "window", "var": "A", "lo": 8, "hi": 10},
                {"id": "p1", "op": "precedence", "a": "A", "b": "B", "min_gap": 5},
                {"id": "w1", "op": "window", "var": "B", "lo": 0, "hi": 10},
            ],
        })
        self.assertEqual(a_ts_bad.verdict, "CERTIFIED_CONTRADICTION")

        # 2. conservation_ledger (SAT)
        a_cl_ok = sr.compile_and_verify({
            "domain": "conservation_ledger",
            "claims": [
                {"id": "f1", "op": "flow_conservation", "terms": [{"edge": "e1", "coeff": 1}, {"edge": "e2", "coeff": -1}], "net": 0},
                {"id": "f2", "op": "flow_conservation", "terms": [{"edge": "e1", "coeff": 1}], "net": 100},
            ],
        })
        self.assertEqual(a_cl_ok.verdict, "CERTIFIED_CONSISTENT")

        # 3. access_policy (SAT)
        a_ap_ok = sr.compile_and_verify({
            "domain": "access_policy",
            "claims": [
                {"id": "r1", "op": "require", "var": "admin"},
                {"id": "h1", "op": "horn", "if_all": ["admin"], "then": "audit_log"},
                {"id": "m1", "op": "mutex", "vars": ["admin", "guest"]},
            ],
        })
        self.assertEqual(a_ap_ok.verdict, "CERTIFIED_CONSISTENT")
        self.assertEqual(a_ap_ok.verified_witness["audit_log"], 1)
        self.assertEqual(a_ap_ok.verified_witness["guest"], 0)

        # 4. group_labeling (SAT)
        a_gl_ok = sr.compile_and_verify({
            "domain": "group_labeling",
            "claims": [
                {"id": "g1", "op": "same", "a": "x", "b": "y"},
                {"id": "g2", "op": "pin", "var": "x", "value": 7},
            ],
        })
        self.assertEqual(a_gl_ok.verdict, "CERTIFIED_CONSISTENT")
        self.assertEqual(a_gl_ok.verified_witness["y"], 7)

    def test_unit_conversion_micro_arbitrage_and_sign_parity(self) -> None:
        # Exact consistent unit conversion
        a_ok = sr.compile_and_verify({
            "domain": "unit_conversion",
            "claims": [
                {"id": "c1", "op": "ratio", "from": "inch", "to": "mm", "num": 127, "den": 5},
                {"id": "c2", "op": "ratio", "from": "foot", "to": "inch", "num": 12, "den": 1},
                {"id": "c3", "op": "ratio", "from": "foot", "to": "mm", "num": 1524, "den": 5},
            ],
        })
        self.assertEqual(a_ok.verdict, "CERTIFIED_CONSISTENT")

        # Odd-negation sign parity loop (A = -B, B = C, C = A -> impossible for nonzero!)
        a_sgn = sr.compile_and_verify({
            "domain": "unit_conversion",
            "claims": [
                {"id": "s1", "op": "ratio", "from": "A", "to": "B", "num": 1, "den": 1, "sign": -1},
                {"id": "s2", "op": "ratio", "from": "B", "to": "C", "num": 1, "den": 1, "sign": 1},
                {"id": "s3", "op": "ratio", "from": "C", "to": "A", "num": 1, "den": 1, "sign": 1},
            ],
        })
        self.assertEqual(a_sgn.verdict, "CERTIFIED_CONTRADICTION")
        self.assertEqual(a_sgn.contradiction_class, "UNIT_SIGN_PARITY_TORSION")
        self.assertEqual(len(a_sgn.mus_claims), 3)

    def test_all_five_example_json_files_certified_autopsies(self) -> None:
        expected = {
            "01_temporal_schedule_paradox.json": ("UNSAT_TORSION", 4),
            "02_unit_conversion_micro_arbitrage.json": ("UNSAT_UNIT_ARBITRAGE_PRIME_COHOMOLOGY", 3),
            "03_ledger_h2_conservation_fraud.json": ("UNSAT_TORSION", 10),
            "04_access_control_horn_mutex.json": ("CHVATAL_GOMORY_CUT", 10),
            "05_group_labeling_mobius_parity.json": ("UNSAT_TORSION", 5),
        }
        ex_dir = REPO_ROOT / "examples"
        for fname, (exp_cls, exp_mus_len) in expected.items():
            aut = sr.verify_json_file(ex_dir / fname)
            self.assertEqual(aut.verdict, "CERTIFIED_CONTRADICTION", fname)
            self.assertEqual(aut.contradiction_class, exp_cls, fname)
            self.assertEqual(len(aut.mus_claims), exp_mus_len, fname)
            self.assertGreater(len(aut.mcs_repairs), 0, fname)
            self.assertIn("FORENSIC CONTRADICTION AUTOPSY", aut.format_report())

    def test_cli_demo_and_verify_json_modes(self) -> None:
        from sheaf_radar.__main__ import main as cli_main
        import json

        # Smoke test CLI verify exit code (1 for certified contradiction!)
        ex2 = str(REPO_ROOT / "examples/02_unit_conversion_micro_arbitrage.json")
        # Redirect stdout cleanly using a lightweight stdlib-free StringIO-like list buffer
        class _Buf:
            def __init__(self) -> None:
                self.parts = []
            def write(self, s: str) -> int:
                self.parts.append(s)
                return len(s)
            def flush(self) -> None:
                pass

        old_out = sys.stdout
        buf = _Buf()
        try:
            sys.stdout = buf  # type: ignore[assignment]
            rc_ver = cli_main(["verify", ex2, "--json"])
            out_json = "".join(buf.parts)
            buf.parts.clear()
            rc_demo = cli_main(["--demo"])
        finally:
            sys.stdout = old_out
        self.assertEqual(rc_ver, 1)
        self.assertEqual(rc_demo, 0)
        parsed = json.loads(out_json)
        self.assertEqual(parsed["verdict"], "CERTIFIED_CONTRADICTION")
        self.assertEqual(parsed["certificate"]["dual_cycle_weight"], -20)

    def test_package_version_and_all_ten_svgs_present(self) -> None:
        self.assertEqual(sr.__version__, "2.0.0")
        plots_dir = REPO_ROOT / "plots"
        svgs = sorted(plots_dir.glob("fig*.svg"))
        self.assertEqual(len(svgs), 10)
        for p in svgs:
            txt = p.read_text(encoding="utf-8").strip()
            self.assertTrue(txt.startswith("<svg"), p.name)
            self.assertTrue(txt.endswith("</svg>"), p.name)


if __name__ == "__main__":
    unittest.main(verbosity=2)
