"""Command-line interface for sheaf-radar-over-Z-and-Q v2.0.0.

Usage:
    python3 -m sheaf_radar verify <path.json> [--json]
    python3 -m sheaf_radar --demo

Strictly Python 3 standard library only.
"""

import argparse
import json
from pathlib import Path
import sys
from typing import List, Optional

from . import __version__, sophist
from .claim_compiler import compile_and_verify, verify_json_file
from .sparse_exact import solve_torsor, verify_torsor_certificate
from .streaming_firewall import FirewallClaim, IncrementalSheafFirewall
from .tarski_hybrid import solve_hybrid_torsor_tarski


def _run_demo() -> int:
    print("=" * 78)
    print(f"SHEAF RADAR v{__version__} — ZERO-DEPENDENCY EXACT Z/Q/TARSKI INTERACTIVE DEMO")
    print("=" * 78)

    # 1. Cycle 5: Unpeelable 3-Regular Tseitin Z/6Z Expander (0% DHSW Peel)
    B, c_exp, _ = sophist.build_unpeelable_tseitin_expander(N=60, modulus=6, defect=1, seed=20261119)
    r_exp = solve_torsor(B, c_exp, ring="Z", want_witness=True)
    ok_exp, _ = verify_torsor_certificate(B, c_exp, r_exp)
    print(f"\n[1/4] Unpeelable 3-Regular Tseitin Z/6Z Expander (N=60, 0% peel):")
    print(f"      Status={r_exp.status} | Single |D1|={r_exp.single_det_D1_bits}b -> Double-Det G={r_exp.double_det_G} "
          f"({r_exp.double_det_G.bit_length() if r_exp.double_det_G else 0}b) | Cert Verified={ok_exp}")

    # 2. Cycle 6: 3-Pentagon KCBS Quantum Contextuality CG Ghost
    A_k, c_k, lo_k, hi_k = sophist.build_coupled_kcbs_pentagon_cg_ghost()
    r_k = solve_hybrid_torsor_tarski(A_k, c_k, lo_k, hi_k)
    print(f"\n[2/4] 3-Pentagon KCBS Quantum Contextuality Ghost (30 vars, LP feasible at 7/15):")
    print(f"      Verdict={r_k.sound_verdict} | Stage={r_k.proof_stage} | "
          f"CG Cuts={len(r_k.cg_cuts_derived)} | Branches={r_k.bb_nodes_explored} | Time={r_k.elapsed_ms:.2f} ms")

    # 3. Cycle 7: Streaming Pre-Commit Sheaf Firewall (120-hop Z_2 Liar Flip!)
    fw = IncrementalSheafFirewall(ring="Z")
    for i in range(120):
        fw.commit_claim(FirewallClaim(i + 1, "affine_1d", {"u": i, "v": i + 1, "coeff_u": -1, "coeff_v": 1, "rhs": 0}))
    v_liar = fw.commit_claim(FirewallClaim(121, "affine_1d", {"u": 0, "v": 120, "coeff_u": -1, "coeff_v": 1, "rhs": 1}))
    print(f"\n[3/4] Streaming Pre-Commit Sheaf Firewall (120-hop Z_2 Liar Flip):")
    print(f"      Accepted={v_liar.accepted} | Path={v_liar.path_taken} | Cert={v_liar.torsion_cert} | "
          f"MUS={len(v_liar.mus_claim_ids or [])} claims | Latency={v_liar.latency_us:.2f} us")

    # 4. Cycle 8: Run all 5 real-world examples/*.json if present, else inline 5-domain showcase
    examples_dir = Path(__file__).resolve().parent.parent / "examples"
    ex_files = sorted(examples_dir.glob("*.json")) if examples_dir.is_dir() else []
    print(f"\n[4/4] 5-Domain Forensic Claim Compiler ({len(ex_files)} JSON examples found):")
    if ex_files:
        for exf in ex_files:
            aut = verify_json_file(exf)
            print(f"  * {exf.name:46s} -> {aut.verdict} ({aut.contradiction_class or 'OK'}, "
                  f"MUS={len(aut.mus_claims)}, repairs={len(aut.mcs_repairs)}, {aut.elapsed_ms:.2f} ms)")
    else:
        aut = compile_and_verify({
            "domain": "unit_conversion",
            "title": "Inline Micro-Arbitrage Loop",
            "claims": [
                {"id": "c1", "op": "ratio", "from": "A", "to": "B", "num": 2, "den": 1},
                {"id": "c2", "op": "ratio", "from": "B", "to": "A", "num": 10**17 + 1, "den": 2 * (10**17)},
            ],
        })
        print(aut.format_report())

    print("\n" + "=" * 78)
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        prog="python3 -m sheaf_radar",
        description=f"sheaf-radar-over-Z-and-Q v{__version__} — Exact Z/Q/Tarski Contradiction Radar CLI",
    )
    parser.add_argument("--version", action="version", version=f"sheaf-radar-over-Z-and-Q {__version__}")
    parser.add_argument("--demo", action="store_true", help="Run interactive v2.0.0 capability & 5-domain demo")

    subparsers = parser.add_subparsers(dest="command")
    p_ver = subparsers.add_parser("verify", help="Compile & zero-trust verify a JSON claim specification")
    p_ver.add_argument("path", type=str, help="Path to JSON claim specification file")
    p_ver.add_argument("--json", action="store_true", dest="as_json", help="Emit machine-readable JSON autopsy")

    args = parser.parse_args(argv)
    if args.demo:
        return _run_demo()
    if args.command == "verify":
        target = Path(args.path)
        if not target.is_file():
            print(f"Error: file not found: {target}", file=sys.stderr)
            return 2
        aut = verify_json_file(target)
        if args.as_json:
            print(json.dumps(aut.to_dict(), indent=2))
        else:
            print(aut.format_report())
        return 0 if aut.verdict == "CERTIFIED_CONSISTENT" else 1

    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
