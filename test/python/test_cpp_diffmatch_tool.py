import importlib.util
import json
import subprocess
import sys

from smack_test_paths import REPO_ROOT, clang_path, llvm_link_path, run_with_timeout, tool_path


def load_svf_adapter_module():
    module_path = REPO_ROOT / "tools" / "svf_memory_partition_adapter.py"
    spec = importlib.util.spec_from_file_location("svf_memory_partition_adapter", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def compile_c_to_bc(tmp_path, name, source):
    src = tmp_path / f"{name}.c"
    bc = tmp_path / f"{name}.bc"
    src.write_text(source)
    run_with_timeout(
        [
            clang_path(),
            "-c",
            "-emit-llvm",
            "-O0",
            "-g",
            "-gcolumn-info",
            "-Xclang",
            "-disable-O0-optnone",
            "-o",
            str(bc),
            str(src),
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )
    return bc


def compile_support_lib_to_bc(tmp_path, lib_name):
    source = REPO_ROOT / "share" / "smack" / "lib" / lib_name
    bc = tmp_path / f"{lib_name}.bc"
    run_with_timeout(
        [
            clang_path(),
            "-c",
            "-emit-llvm",
            "-O0",
            "-g",
            "-gcolumn-info",
            "-Wno-error=implicit-function-declaration",
            "-Wno-error=implicit-int",
            "-Wno-error=int-conversion",
            "-Wno-error=incompatible-pointer-types",
            "-Xclang",
            "-disable-O0-optnone",
            f"-I{REPO_ROOT / 'share' / 'smack' / 'include'}",
            "-DMEMORY_MODEL_NO_REUSE_IMPLS",
            "-o",
            str(bc),
            str(source),
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )
    return bc


def link_with_smack_support(tmp_path, name, bc):
    linked = tmp_path / f"{name}-linked.bc"
    support = [
        compile_support_lib_to_bc(tmp_path, "smack.c"),
        compile_support_lib_to_bc(tmp_path, "stdlib.c"),
        compile_support_lib_to_bc(tmp_path, "errno.c"),
        compile_support_lib_to_bc(tmp_path, "smack-rust.c"),
    ]
    run_with_timeout(
        [llvm_link_path(), "-o", str(linked), str(bc), *map(str, support)],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )
    return linked


def build_empty_svf_oracle(tmp_path, name, linked, *, sea_dsa_mode="ci"):
    adapter = load_svf_adapter_module()
    pre_ll = tmp_path / f"{name}.pre.ll"
    oracle_path = tmp_path / f"{name}.oracle.json"
    completed = run_with_timeout(
        [
            tool_path("llvm2bpl"),
            str(linked),
            f"-sea-dsa={sea_dsa_mode}",
            "-smack-memory-partitioner=sea-dsa",
            f"--ll={pre_ll}",
            "-warn-type",
            "silent",
            "-source-loc-syms",
            "-provenance-syms",
            "-entry-points",
            "f",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )
    assert completed.returncode == 0, completed.stdout
    oracle = adapter.build_oracle(ll_text=pre_ll.read_text(), svf_output="")
    oracle_path.write_text(json.dumps(oracle, indent=2, sort_keys=True) + "\n")
    return oracle


def write_bundled_oracle(tmp_path, left_linked, right_linked):
    left_oracle = build_empty_svf_oracle(tmp_path, "left", left_linked)
    right_oracle = build_empty_svf_oracle(tmp_path, "right", right_linked)
    modules = {
        left_oracle["module_fingerprint"]: left_oracle,
        right_oracle["module_fingerprint"]: right_oracle,
    }
    bundle = {
        "schema_version": 2,
        "producer": "svf-memory-partition-bundle",
        "analysis": "andersen",
        "memory_partition": "intra-disjoint",
        "modules": modules,
        "stats": {"module_count": len(modules)},
    }
    bundle_path = tmp_path / "svf-memory-partition-bundle.json"
    bundle_path.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n")
    return bundle_path


def run_diffmatch(tmp_path, extra_args=None):
    left_bc = compile_c_to_bc(
        tmp_path,
        "left",
        "int f(int x) {\n  int y = x + 0;\n  return y + 1;\n}\n",
    )
    right_bc = compile_c_to_bc(
        tmp_path,
        "right",
        "int f(int x) {\n  int y = x - 0;\n  return y + 1;\n}\n",
    )
    left_linked = link_with_smack_support(tmp_path, "left", left_bc)
    right_linked = link_with_smack_support(tmp_path, "right", right_bc)
    left_bpl = tmp_path / "left.bpl"
    right_bpl = tmp_path / "right.bpl"
    match_json = tmp_path / "match.json"
    oracle = write_bundled_oracle(tmp_path, left_linked, right_linked)
    cmd = [
        tool_path("llvm-diffmatch2bpl"),
        "--left-bc",
        str(left_linked),
        "--right-bc",
        str(right_linked),
        "--left-entry",
        "f",
        "--right-entry",
        "f",
        "--left-bpl",
        str(left_bpl),
        "--right-bpl",
        str(right_bpl),
        "--match-json",
        str(match_json),
        "-warn-type",
        "silent",
        "-sea-dsa=ci",
        f"-smack-memory-partition-oracle={oracle}",
        "-source-loc-syms",
        "-provenance-syms",
        "-entry-points",
        "f",
    ]
    if extra_args:
        cmd.extend(extra_args)
    completed = run_with_timeout(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )
    assert completed.returncode == 0, completed.stdout
    assert left_bpl.exists()
    assert right_bpl.exists()
    assert match_json.exists()
    return left_bpl, right_bpl, json.loads(match_json.read_text())


def test_cpp_diffmatch2bpl_emits_bpl_and_match_json_without_ll_by_default(tmp_path):
    left_bpl, right_bpl, match = run_diffmatch(tmp_path)

    assert "procedure" in left_bpl.read_text()
    assert "procedure" in right_bpl.read_text()
    assert match["source"] == "smack-cpp"
    assert match["chunks"]
    assert match["stats"]["left_blocks"] >= 1
    assert match["stats"]["right_blocks"] >= 1
    assert match["stats"]["left_instructions"] >= 1
    assert match["stats"]["right_instructions"] >= 1
    assert match["stats"]["matcher_ms"] >= 0
    assert not (tmp_path / "left.ll").exists()
    assert not (tmp_path / "right.ll").exists()


def test_cpp_diffmatch2bpl_dumps_ll_only_when_requested(tmp_path):
    run_diffmatch(
        tmp_path,
        [
            "--left-ll",
            str(tmp_path / "left.ll"),
            "--right-ll",
            str(tmp_path / "right.ll"),
        ],
    )

    assert "define" in (tmp_path / "left.ll").read_text()
    assert "define" in (tmp_path / "right.ll").read_text()
