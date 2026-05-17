import importlib.util
import json
import subprocess
import sys

from smack_test_paths import (
    REPO_ROOT,
    clang_path,
    clangxx_path,
    llvm_link_path,
    run_with_timeout,
    tool_path,
)


def load_svf_adapter_module():
    module_path = REPO_ROOT / "tools" / "svf_memory_partition_adapter.py"
    spec = importlib.util.spec_from_file_location("svf_memory_partition_adapter", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def compile_source_to_linked_bc(tmp_path, name, source, *, cxx=False):
    suffix = "cpp" if cxx else "c"
    src = tmp_path / f"{name}.{suffix}"
    bc = tmp_path / f"{name}.bc"
    runtime_bc = tmp_path / f"{name}-smack-runtime.bc"
    linked = tmp_path / f"{name}-linked.bc"
    src.write_text(source)

    compiler = clangxx_path() if cxx else clang_path()
    cmd = [
        compiler,
        "-O0",
        "-g",
        "-emit-llvm",
        "-c",
        str(src),
        "-o",
        str(bc),
    ]
    if cxx:
        cmd.insert(1, "-fno-exceptions")
        cmd.insert(2, "-fno-rtti")
    run_with_timeout(
        cmd,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )

    run_with_timeout(
        [
            clang_path(),
            "-O0",
            "-g",
            "-emit-llvm",
            "-c",
            f"-I{REPO_ROOT / 'share' / 'smack' / 'include'}",
            str(REPO_ROOT / "share" / "smack" / "lib" / "smack.c"),
            "-o",
            str(runtime_bc),
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )

    run_with_timeout(
        [llvm_link_path(), str(bc), str(runtime_bc), "-o", str(linked)],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout_name="LLVM",
        default_timeout=60,
    )
    return linked


def emit_pre_bpl_ll(tmp_path, name, linked, *, entry="f"):
    pre_ll = tmp_path / f"{name}.pre.ll"
    completed = run_with_timeout(
        [
            tool_path("llvm2bpl"),
            "-smack-memory-partitioner=sea-dsa",
            "-smack-skip-devirt",
            f"--ll={pre_ll}",
            f"--entry-points={entry}",
            str(linked),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )
    assert completed.returncode == 0, completed.stdout
    return pre_ll


def run_with_devirt_report(tmp_path, name, source, *, entry="f", cxx=False):
    linked = compile_source_to_linked_bc(tmp_path, name, source, cxx=cxx)
    report = tmp_path / f"{name}.devirt.json"
    bpl = tmp_path / f"{name}.bpl"
    completed = run_with_timeout(
        [
            tool_path("llvm2bpl"),
            "-smack-memory-partitioner=sea-dsa",
            f"-smack-devirt-report={report}",
            f"--bpl={bpl}",
            f"--entry-points={entry}",
            str(linked),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )
    assert completed.returncode == 0, completed.stdout
    return json.loads(report.read_text())


def test_devirt_report_resolves_constant_function_pointer_table(tmp_path):
    source = """
typedef int (*fp_t)(int);
int only(int x) { return x + 1; }
int other(int x) { return x + 2; }
volatile int choose;
fp_t noise = other;
static fp_t const table[1] = { only };
int f(int x) {
  if (choose) return noise(x);
  return table[0](x);
}
"""
    data = run_with_devirt_report(tmp_path, "fp_table", source)

    assert data["schema_version"] == 2
    assert all("callsite_id" in call for call in data["callsites"])
    assert any(
        call["complete"]
        and call["target_count"] == 1
        and call["targets"] == ["only"]
        and call["source"] in {"sea-dsa", "type-dataflow"}
        for call in data["callsites"]
    ), data


def test_devirt_falls_back_for_external_function_pointer_source(tmp_path):
    source = """
typedef int (*fp_t)(int);
extern fp_t unknown_fp(void);
int only(int x) { return x + 1; }
int other(int x) { return x + 2; }
fp_t keep = other;
fp_t keep2 = only;
int f(int x) {
  if (x == 12345) return keep(x);
  if (x == 54321) return keep2(x);
  fp_t p = unknown_fp();
  return p(x);
}
"""
    data = run_with_devirt_report(tmp_path, "fp_external_source", source)

    assert any(
        call["source"] == "fallback"
        and not call["complete"]
        and call["fallback_target_count"] >= 2
        for call in data["callsites"]
    ), data


def test_devirt_uses_complete_svf_indirect_target_oracle(tmp_path):
    adapter = load_svf_adapter_module()
    source = """
typedef int (*fp_t)(int);
extern fp_t unknown_fp(void);
int only(int x) { return x + 1; }
int other(int x) { return x + 2; }
fp_t keep = other;
fp_t keep2 = only;
int f(int x) {
  if (x == 12345) return keep(x);
  if (x == 54321) return keep2(x);
  fp_t p = unknown_fp();
  return p(x);
}
"""
    linked = compile_source_to_linked_bc(tmp_path, "fp_svf_oracle", source)
    pre_ll = emit_pre_bpl_ll(tmp_path, "fp_svf_oracle", linked)
    ll_text = pre_ll.read_text()
    oracle = adapter.build_oracle(ll_text=ll_text, svf_output="")
    indirect_calls = [
        call
        for call in adapter.iter_module_call_infos(ll_text)
        if call.function == "f" and call.indirect
    ]
    assert indirect_calls
    oracle["indirect_call_targets"] = {
        call.key: {"targets": ["only"], "complete": True} for call in indirect_calls
    }
    oracle["stats"]["indirect_call_target_count"] = len(indirect_calls)

    oracle_path = tmp_path / "fp_svf_oracle.oracle.json"
    report = tmp_path / "fp_svf_oracle.devirt.json"
    bpl = tmp_path / "fp_svf_oracle.bpl"
    oracle_path.write_text(json.dumps(oracle, indent=2, sort_keys=True) + "\n")

    completed = run_with_timeout(
        [
            tool_path("llvm2bpl"),
            "-smack-memory-partitioner=svf-refined",
            f"-smack-memory-partition-oracle={oracle_path}",
            f"-smack-devirt-report={report}",
            f"--bpl={bpl}",
            "--entry-points=f",
            str(linked),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
        timeout_name="SMACK_TOOL",
        default_timeout=120,
    )
    assert completed.returncode == 0, completed.stdout
    data = json.loads(report.read_text())

    assert any(
        call["source"] == "svf"
        and call["complete"]
        and call["targets"] == ["only"]
        and call["svf_complete"]
        and call["svf_targets"] == ["only"]
        for call in data["callsites"]
    ), data


def test_devirt_resolves_cpp_vtable_slot_without_same_signature_noise(tmp_path):
    source = """
struct Base {
  virtual int value() { return 1; }
};
struct Derived : Base {
  int value() override { return 2; }
};
extern "C" int other(Base *b) { return b ? 3 : 4; }
using Raw = int (*)(Base *);
Raw keep = other;
extern "C" int f(int c) {
  Base base;
  Derived derived;
  Base *b = c ? &base : &derived;
  return b->value();
}
"""
    data = run_with_devirt_report(tmp_path, "cpp_vtable", source, cxx=True)

    virtual_calls = [
        call
        for call in data["callsites"]
        if call["complete"] and any("value" in target for target in call["targets"])
    ]
    assert virtual_calls, data
    assert all("other" not in target for call in virtual_calls for target in call["targets"])
    assert any(call["target_count"] <= 2 for call in virtual_calls)
