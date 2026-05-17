"""Diff-product orchestration: lower two source versions through SMACK and
build a diff-scoped Boogie product artifact.

Extracted from share/smack/top.py during Phase B5 of the modernization plan.
The dispatcher (`run_diff_product`) is invoked from `top.main` when `--diff-product`
is on the command line. The helpers were all already self-contained in `top.py`;
this module mostly re-arranges imports so the orchestration lives alongside the
existing `share/smack/diffprod/` package.
"""

import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from smack.cli.results import VProperty, VResult
from smack.pipeline.frontend import frontend, target_selection
from smack.pipeline.transform import transform_bpl, transform_out
from smack.pipeline.translate import (
    annotate_bpl,
    generate_svf_memory_partition_oracle,
    memsafety_subproperty_selection,
    replace_reach_error,
)
from smack.utils import try_command
from smack.verifier.commands import (
    boogie_command,
    corral_command,
)
from smack.verifier.runner import verification_result


def _exit_with_error(error):
    sys.exit(f"Error: {error}.")


def run_diff_product(args):
    """Run both source versions through SMACK and build the diff product."""

    from smack.diffprod.failure_cut import failure_cut_from_text
    from smack.diffprod.pipeline import EquivalenceCheck, build_from_bpl

    with tempfile.TemporaryDirectory(prefix="smack-diff-product-") as tmp_dir:
        mode = getattr(args, "diff_product_mode", None) or "patch-with-right"
        diff_text = ""
        right_input = args.diff_right
        right_name = args.diff_right

        if mode in ("patch", "patch-with-right"):
            with Path(args.diff_product).open() as f:
                diff_text = f.read()

        if mode == "patch":
            from tools.smack_diff import apply_unified_diff_to_text

            with Path(args.diff_left).open() as f:
                left_source_text = f.read()
            patched_source_text = apply_unified_diff_to_text(left_source_text, diff_text)
            right_input = str(
                Path(tmp_dir) / diff_product_patched_filename(diff_text, args.diff_left)
            )
            with Path(right_input).open("w") as f:
                f.write(patched_source_text)
            right_name = f"{args.diff_left} (patched)"

        left_args = diff_product_side_args(
            args, args.diff_left, args.diff_left_entry, tmp_dir, "left"
        )
        right_args = diff_product_side_args(
            args, right_input, args.diff_right_entry, tmp_dir, "right"
        )

        target_selection(left_args)
        frontend(left_args)
        target_selection(right_args)
        frontend(right_args)

        lowering = run_paired_diff_product_lowering(args, left_args, right_args, tmp_dir)
        lowering_diagnostics = lowering.get("diagnostics", [])

        if lowering.get("ok"):
            left_bpl = lowering["left_bpl"]
            right_bpl = lowering["right_bpl"]
            llvm_match = lowering.get("llvm_match")
        else:
            _exit_with_error(
                "the required SMACK C++ LLVM matcher could not run: {}. "
                "Build and install SMACK with LLVM 22, then ensure "
                "`llvm-diffmatch2bpl` is on PATH".format("; ".join(lowering_diagnostics))
            )

        if args.diff_product_left_bpl_out:
            with Path(args.diff_product_left_bpl_out).open("w") as f:
                f.write(left_bpl)
        if args.diff_product_right_bpl_out:
            with Path(args.diff_product_right_bpl_out).open("w") as f:
                f.write(right_bpl)

        if args.diff_product_match_json and llvm_match is not None:
            with Path(args.diff_product_match_json).open("w") as f:
                json.dump(llvm_match, f, indent=2, sort_keys=True)
                f.write("\n")

        if (
            args.diff_product_out is None
            and args.diff_product_json is None
            and not args.diff_product_verify
            and not args.diff_product_require_actual
        ):
            if not args.quiet:
                if args.diff_product_left_bpl_out:
                    print(f"SMACK generated {args.diff_product_left_bpl_out}")
                if args.diff_product_right_bpl_out:
                    print(f"SMACK generated {args.diff_product_right_bpl_out}")
                if args.diff_product_match_json:
                    print(f"SMACK generated {args.diff_product_match_json}")
            return

        result = build_from_bpl(
            left_bpl=left_bpl,
            right_bpl=right_bpl,
            diff_text=diff_text,
            left_name=args.diff_left,
            right_name=right_name,
            left_entry=args.diff_left_entry,
            right_entry=args.diff_right_entry,
            alignment=args.diff_product_alignment,
            no_egraph=args.diff_product_no_egraph,
            egraph_timeout_s=args.diff_product_egraph_timeout,
            llvm_match=llvm_match,
        )
        result.diagnostics = [
            "interface mode: %s"
            % ("patch" if mode in ("patch", "patch-with-right") else "functions"),
            *lowering_diagnostics,
            *result.diagnostics,
        ]

    if args.diff_product_out is not None:
        with Path(args.diff_product_out).open("w") as f:
            f.write(result.product.text)

    if args.diff_product_verify:
        verifier_output, verifier_result = verify_diff_product(args)
        result.equivalence = EquivalenceCheck(
            checked=True,
            verified=verifier_result is VResult.VERIFIED,
            result=str(verifier_result),
            return_code=verifier_result.return_code(),
            output_tail=verifier_output[-4000:],
        )
        result.failure_cut = failure_cut_from_text(result.left, result.right, verifier_output)

    report_file = args.diff_product_json or args.json_file
    if report_file:
        with Path(report_file).open("w") as f:
            json.dump(result.to_json(), f, indent=2, sort_keys=True)
            f.write("\n")

    if not args.quiet:
        if args.diff_product_out is not None:
            print(f"SMACK generated {args.diff_product_out}")
        if args.diff_product_left_bpl_out:
            print(f"SMACK generated {args.diff_product_left_bpl_out}")
        if args.diff_product_right_bpl_out:
            print(f"SMACK generated {args.diff_product_right_bpl_out}")
        if report_file:
            print(f"SMACK generated {report_file}")

    if args.diff_product_require_actual and not result.product.actual_product_available:
        _exit_with_error(
            "--diff-product-require-actual was set, but only metadata fallback was available"
        )


def run_paired_diff_product_lowering(args, left_args, right_args, tmp_dir):
    """Run the paired SMACK LLVM matcher/lowerer when it is available."""

    match_file = str(Path(tmp_dir) / "llvm-match.json")
    oracle_file = getattr(args, "memory_partition_oracle", None)
    if (
        args.memory_partitioner == "svf-refined"
        and not oracle_file
        and not args.no_memory_splitting
    ):
        oracle_file = generate_paired_svf_memory_partition_oracle(
            args, left_args, right_args, tmp_dir
        )
    cmd = [
        "llvm-diffmatch2bpl",
        "--left-bc",
        left_args.linked_bc_file,
        "--right-bc",
        right_args.linked_bc_file,
        "--left-entry",
        args.diff_left_entry,
        "--right-entry",
        args.diff_right_entry,
        "--left-bpl",
        left_args.bpl_file,
        "--right-bpl",
        right_args.bpl_file,
        "--match-json",
        match_file,
    ]
    if args.diff_product_dump_llvm:
        cmd += ["--left-ll", left_args.ll_file]
        cmd += ["--right-ll", right_args.ll_file]
    if args.diff_product_structured_bpl_loops:
        cmd += ["--structured-bpl-loops"]
    if args.diff_product_structured_bpl_loops_strict:
        cmd += ["--structured-bpl-loops-strict"]
    cmd += llvm_to_bpl_option_args(
        args,
        [args.diff_left_entry, args.diff_right_entry],
        memory_partition_oracle=oracle_file,
    )

    if args.debug:
        print("Running {}".format(" ".join(cmd)))

    try:
        completed = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
    except OSError as err:
        return {
            "ok": False,
            "diagnostics": [
                f"SMACK C++ LLVM matcher unavailable: {err}",
            ],
        }

    if completed.returncode != 0:
        tail = completed.stdout[-1200:].strip()
        return {
            "ok": False,
            "diagnostics": [
                "SMACK C++ LLVM matcher failed with exit code {}{}".format(
                    completed.returncode,
                    (f": {tail}") if tail else "",
                ),
            ],
        }

    for side_args in (left_args, right_args):
        annotate_bpl(side_args)
        memsafety_subproperty_selection(side_args)
        replace_reach_error(side_args)
        transform_bpl(side_args)

    with Path(left_args.bpl_file).open() as f:
        left_bpl = f.read()
    with Path(right_args.bpl_file).open() as f:
        right_bpl = f.read()
    with Path(match_file).open() as f:
        llvm_match = json.load(f)

    return {
        "ok": True,
        "left_bpl": left_bpl,
        "right_bpl": right_bpl,
        "llvm_match": llvm_match,
        "diagnostics": ["LLVM matcher source: smack-cpp"],
    }


def generate_paired_svf_memory_partition_oracle(args, left_args, right_args, tmp_dir):
    """Generate and bundle per-side SVF oracles for paired lowering."""

    entry_points = []
    for ep in (args.diff_left_entry, args.diff_right_entry):
        if ep and ep not in entry_points:
            entry_points.append(ep)

    left_oracle_args = copy.copy(left_args)
    right_oracle_args = copy.copy(right_args)
    left_oracle_args.entry_points = entry_points
    right_oracle_args.entry_points = entry_points
    for name in (
        "svf_wpa",
        "svf_extapi",
        "svf_mem_par",
        "svf_timeout",
        "svf_indirect_calls",
        "svf_loop_diagnostics",
        "svf_saber_diagnostics",
        "svf_mta_diagnostics",
    ):
        if hasattr(args, name):
            setattr(left_oracle_args, name, getattr(args, name))
            setattr(right_oracle_args, name, getattr(args, name))

    left_oracle_path = Path(generate_svf_memory_partition_oracle(left_oracle_args))
    right_oracle_path = Path(generate_svf_memory_partition_oracle(right_oracle_args))
    left_oracle = json.loads(left_oracle_path.read_text())
    right_oracle = json.loads(right_oracle_path.read_text())

    modules = {
        left_oracle["module_fingerprint"]: left_oracle,
        right_oracle["module_fingerprint"]: right_oracle,
    }
    bundle = {
        "schema_version": 2,
        "producer": "svf-memory-partition-bundle",
        "analysis": left_oracle.get("analysis", "andersen"),
        "memory_partition": left_oracle.get("memory_partition", "intra-disjoint"),
        "modules": modules,
        "stats": {
            "module_count": len(modules),
            "left_module_fingerprint": left_oracle["module_fingerprint"],
            "right_module_fingerprint": right_oracle["module_fingerprint"],
        },
    }

    bundle_path = Path(tmp_dir) / "svf-memory-partition-bundle.json"
    bundle_path.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n")
    return str(bundle_path)


def llvm_to_bpl_option_args(args, entry_points, memory_partition_oracle=None):
    """Build the llvm2bpl-compatible options shared by product lowerers."""

    cmd = ["-warn-type", args.warn]
    cmd += ["-sea-dsa=bu"]
    if sys.stdout.isatty():
        cmd += ["-colored-warnings"]
    cmd += ["-source-loc-syms"]
    cmd += ["-provenance-syms"]
    seen = set()
    for ep in entry_points:
        if ep and ep not in seen:
            cmd += ["-entry-points", ep]
            seen.add(ep)
    for cf in args.checked_functions:
        cmd += ["-checked-functions", cf]
    if args.debug:
        cmd += ["-debug"]
    if args.debug_only:
        cmd += ["-debug-only", args.debug_only]
    if "impls" in args.mem_mod:
        cmd += ["-mem-mod-impls"]
    if args.static_unroll:
        cmd += ["-static-unroll"]
    if args.integer_encoding == "bit-vector":
        cmd += ["-bit-precise"]
    if args.integer_encoding == "wrapped-integer":
        cmd += ["-wrapped-integer-encoding"]
    if args.timing_annotations:
        cmd += ["-timing-annotations"]
    if args.pointer_encoding == "bit-vector":
        cmd += ["-bit-precise-pointers"]
    if args.no_byte_access_inference:
        cmd += ["-no-byte-access-inference"]
    if args.rewrite_bitwise_ops:
        cmd += ["-rewrite-bitwise-ops"]
    if args.no_memory_splitting:
        cmd += ["-no-memory-splitting"]
    cmd += ["-smack-memory-partitioner", args.memory_partitioner]
    oracle = memory_partition_oracle or getattr(args, "memory_partition_oracle", None)
    if oracle:
        cmd += ["-smack-memory-partition-oracle", oracle]
    if getattr(args, "svf_loop_frames", False):
        cmd += ["-smack-svf-loop-frames"]
    if getattr(args, "svf_call_frames", False):
        cmd += ["-smack-svf-call-frames"]
    if getattr(args, "svf_indirect_calls", False):
        cmd += ["-smack-svf-indirect-calls"]
    if getattr(args, "svf_analysis", None):
        cmd += ["-smack-svf-analysis", str(args.svf_analysis)]
    if getattr(args, "svf_mem_par", None):
        cmd += ["-smack-svf-mem-par", str(args.svf_mem_par)]
    if getattr(args, "svf_extapi", None):
        cmd += ["-smack-svf-extapi", str(args.svf_extapi)]
    if args.static_init_zero_memset_threshold is not None:
        cmd += [
            "-static-init-zero-memset-threshold",
            str(args.static_init_zero_memset_threshold),
        ]
    if args.check.contains_mem_safe_props():
        cmd += ["-memory-safety"]
    if VProperty.INTEGER_OVERFLOW in args.check:
        cmd += ["-integer-overflow"]
    if VProperty.RUST_PANICS in args.check:
        cmd += ["-rust-panics"]
    if args.fail_on_loop_exit:
        cmd += ["-fail-on-loop-exit"]
    if args.llvm_assumes:
        cmd += ["-llvm-assumes=" + args.llvm_assumes]
    if args.float:
        cmd += ["-float"]
    if args.modular:
        cmd += ["-modular"]
    return cmd


def diff_product_patched_filename(diff_text, fallback_source):
    """Choose a temp filename that matches the diff's right-side source path."""

    for line in diff_text.splitlines():
        if not line.startswith("+++ "):
            continue
        path = line[4:].split("\t", 1)[0].strip()
        if path == "/dev/null":
            break
        if path.startswith("a/") or path.startswith("b/"):
            path = path[2:]
        basename = Path(path).name
        if basename:
            if not Path(basename).suffix:
                fallback_ext = Path(fallback_source).suffix
                basename += fallback_ext or ".c"
            return basename
    ext = Path(fallback_source).suffix
    return "right%s" % (ext or ".c")


def diff_product_side_args(args, input_file, entry_point, tmp_dir, side):
    side_args = copy.copy(args)
    side_args.input_files = [input_file]
    side_args.entry_points = [entry_point]
    side_args.bc_file = str(Path(tmp_dir) / f"{side}.bc")
    side_args.linked_bc_file = str(Path(tmp_dir) / f"{side}-linked.bc")
    side_args.bpl_file = str(Path(tmp_dir) / f"{side}.bpl")
    side_args.ll_file = str(Path(tmp_dir) / f"{side}.ll")
    side_args.no_verify = True
    side_args.provenance_syms = True
    side_args.diff_product = None
    side_args.diff_left = None
    side_args.diff_right = None
    side_args.diff_product_out = None
    side_args.diff_product_json = None
    side_args.diff_product_require_actual = False
    side_args.diff_product_verify = False
    side_args.skip_llvm_to_bpl = True
    return side_args


def verify_diff_product(args):
    """Run the selected diff-product Boogie file and return raw verifier output."""

    verify_args = copy.copy(args)
    verify_args.bpl_file = args.diff_product_out
    verify_args.json_file = None
    verify_args.error_file = None
    verify_args.replay = None

    if verify_args.verifier == "boogie" or verify_args.modular:
        command = boogie_command(verify_args)
        command += ["/proverOpt:O:smt.array.extensional=false"]
        command += ["/proverOpt:O:smt.qi.eager_threshold=100"]
        command += ["/proverOpt:O:smt.arith.solver=2"]
        if verify_args.verifier_options:
            command += verify_args.verifier_options.split()
        command += [verify_args.bpl_file]
    elif verify_args.verifier == "corral":
        command = corral_command(verify_args)
        command += ["/bopt:proverOpt:O:smt.qi.eager_threshold=100"]
        command += ["/bopt:proverOpt:O:smt.arith.solver=2"]
        if verify_args.verifier_options:
            command += verify_args.verifier_options.split()
    else:
        _exit_with_error("--diff-product-verify supports boogie and corral")

    verifier_output = try_command(command, timeout=verify_args.time_limit)
    verifier_output = transform_out(verify_args, verifier_output)
    return verifier_output, verification_result(verifier_output, verify_args.verifier)
