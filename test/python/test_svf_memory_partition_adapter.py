import importlib.util
import json
import sys

from smack_test_paths import REPO_ROOT


def load_adapter_module():
    module_path = REPO_ROOT / "tools" / "svf_memory_partition_adapter.py"
    spec = importlib.util.spec_from_file_location("svf_memory_partition_adapter", module_path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_iter_module_access_keys_preserves_function_and_instruction_order():
    adapter = load_adapter_module()
    ll_text = """
define dso_local i32 @main() {
entry:
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4, !verifier.code !10
  %2 = load i32, ptr %1, align 4, !dbg !11, !verifier.code !10
  ret i32 %2
}
"""

    keys = adapter.iter_module_access_keys(ll_text)

    assert keys == [
        "main\tstore i32 0, ptr %1, align 4",
        "main\t%2 = load i32, ptr %1, align 4",
    ]


def test_parse_svf_dump_maps_load_mu_and_store_chi_to_instruction_keys():
    adapter = load_adapter_module()
    output = """
==========FUNCTION: main==========

LDMU(MR_8V_2) \tpts{1 }
IntraICFGNode1 {fun: main{ "ln": 1 }}
LoadStmt: [Var2 <-- Var1]\t
ValVar ID: 2
   %2 = load i32, ptr %1, align 4, !dbg !11, !verifier.code !10 { "ln": 2, "fl": "x.c" }
IntraICFGNode2 {fun: main{ "ln": 3 }}
StoreStmt: [Var1 <-- Var2]\t
ValVar ID: 3
   store i32 %2, ptr %1, align 4, !dbg !12, !verifier.code !10 { "ln": 3, "fl": "x.c" }
8V_3 = STCHI(MR_8V_2) \tpts{1 }
9V_1 = STCHI(MR_9V_0) \tpts{2 }
"""

    access_regions = adapter.parse_svf_dump(output)

    assert access_regions == {
        "main\t%2 = load i32, ptr %1, align 4": {"MR_8"},
        "main\tstore i32 %2, ptr %1, align 4": {
            "MR_8",
            "MR_9",
        },
    }


def test_build_oracle_filters_unmatched_svf_keys_and_records_fingerprint():
    adapter = load_adapter_module()
    ll_text = """
define dso_local i32 @main() {
entry:
  store i32 0, ptr %1, align 4, !verifier.code !10
  %2 = load i32, ptr %1, align 4, !dbg !11, !verifier.code !10
  ret i32 %2
}
"""
    svf_output = """
==========FUNCTION: main==========
LDMU(MR_8V_2) \tpts{1 }
LoadStmt: [Var2 <-- Var1]\t
   %2 = load i32, ptr %1, align 4, !dbg !11, !verifier.code !10 { "ln": 2, "fl": "x.c" }
StoreStmt: [Var1 <-- Var2]\t
   store i32 0, ptr %1, align 4, !verifier.code !10 { "ln": 3, "fl": "x.c" }
8V_3 = STCHI(MR_8V_2) \tpts{1 }
StoreStmt: [Var4 <-- Var5]\t
   store i32 1, ptr %4, align 4 { "ln": 4, "fl": "x.c" }
9V_1 = STCHI(MR_9V_0) \tpts{2 }
"""

    oracle = adapter.build_oracle(ll_text=ll_text, svf_output=svf_output)

    keys = adapter.iter_module_access_keys(ll_text)
    assert oracle["schema_version"] == 3
    assert oracle["producer"] == "svf-memory-partition-adapter"
    assert oracle["module_fingerprint"] == adapter.fnv1a64(keys)
    assert oracle["access_regions"] == {
        "main\t%2 = load i32, ptr %1, align 4": ["MR_8"],
        "main\tstore i32 0, ptr %1, align 4": ["MR_8"],
    }
    assert oracle["stats"]["module_access_count"] == 2
    assert oracle["stats"]["matched_access_count"] == 2
    assert oracle["stats"]["unmatched_svf_access_count"] == 1
    assert oracle["function_effects"]["main"]["complete"] is True
    assert oracle["loop_effects"] == {}


def test_sanitize_ir_for_svf_rewrites_struct_gep_field_index_only():
    adapter = load_adapter_module()
    ll_text = """
%struct.jacobian.27 = type { [3 x [19 x i32]] }

define void @f(ptr %p) {
  %1 = getelementptr inbounds %struct.jacobian.27, ptr %p, i32 0, i64 0, i64 2
  %2 = load i32, ptr %p, align 4
  ret void
}
"""

    sanitized, count = adapter.sanitize_ir_for_svf(ll_text)

    assert count == 1
    assert "ptr %p, i32 0, i32 0, i64 2" in sanitized
    assert "%2 = load i32, ptr %p, align 4" in sanitized


def test_sanitize_ir_for_svf_truncates_invalid_union_variant_gep():
    adapter = load_adapter_module()
    ll_text = """
%struct.br_x509_pkey = type { i8, %union.anon.17 }
%union.anon.17 = type { %struct.br_rsa_public_key }
%struct.br_rsa_public_key = type { ptr, i64 }

define void @f(ptr %p) {
  %1 = getelementptr inbounds %struct.br_x509_pkey, ptr %p, i32 0, i32 1, i32 1
  %2 = getelementptr inbounds %struct.br_x509_pkey, ptr %p, i32 0, i32 1, i32 0
  ret void
}
"""

    sanitized, count = adapter.sanitize_ir_for_svf(ll_text)

    assert count == 1
    assert (
        "%1 = getelementptr inbounds %struct.br_x509_pkey, ptr %p, i32 0, i32 1"
        in sanitized
    )
    assert (
        "%1 = getelementptr inbounds %struct.br_x509_pkey, ptr %p, i32 0, i32 1, i32 1"
        not in sanitized
    )
    assert (
        "%2 = getelementptr inbounds %struct.br_x509_pkey, ptr %p, i32 0, i32 1, i32 0"
        in sanitized
    )


def test_build_oracle_records_callsite_and_function_effects():
    adapter = load_adapter_module()
    ll_text = """
define dso_local void @callee(ptr %p) {
  store i32 1, ptr %p, align 4
  ret void
}

define dso_local void @main(ptr %p) {
  call void @callee(ptr %p), !dbg !12, !verifier.code !10
  ret void
}
"""
    svf_output = """
==========FUNCTION: callee==========
StoreStmt: [Var1 <-- Var2]\t
   store i32 1, ptr %p, align 4 { "ln": 1, "fl": "x.c" }
8V_1 = STCHI(MR_8V_0) \tpts{1 }
==========FUNCTION: main==========
CALMU(MR_8V_0) \tpts{1 }
CallICFGNode1 {fun: main}
   call void @callee(ptr %p), !dbg !12, !verifier.code !10 CallICFGNode: {fun: main}
8V_2 = CALCHI(MR_8V_0) \tpts{1 }
"""

    oracle = adapter.build_oracle(ll_text=ll_text, svf_output=svf_output)

    call_key = "main\tcall void @callee(ptr %p)"
    assert oracle["callsite_effects"][call_key] == {
        "ref_regions": ["MR_8"],
        "mod_regions": ["MR_8"],
        "complete": True,
    }
    assert oracle["function_effects"]["main"] == {
        "ref_regions": ["MR_8"],
        "mod_regions": ["MR_8"],
        "complete": True,
    }
    assert oracle["stats"]["matched_callsite_effect_count"] == 1


def test_unknown_external_call_makes_function_effect_incomplete():
    adapter = load_adapter_module()
    ll_text = """
declare void @external(ptr)

define dso_local void @main(ptr %p) {
  call void @external(ptr %p)
  ret void
}
"""
    svf_output = """
==========FUNCTION: main==========
CALMU(MR_9V_0) \tpts{1 }
CallICFGNode1 {fun: main}
   call void @external(ptr %p) CallICFGNode: {fun: main}
"""

    oracle = adapter.build_oracle(ll_text=ll_text, svf_output=svf_output)

    assert oracle["function_effects"]["main"]["complete"] is False
    assert oracle["callsite_effects"]["main\tcall void @external(ptr %p)"]["complete"] is False
    assert oracle["stats"]["incomplete_function_effect_count"] == 1


def test_build_oracle_records_loop_effects_from_backedge_metadata():
    adapter = load_adapter_module()
    ll_text = """
define dso_local i32 @main(ptr %p, i32 %n) {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %ok = icmp slt i32 %i, %n
  br i1 %ok, label %body, label %exit
body:
  store i32 %i, ptr %p, align 4
  %next = add nsw i32 %i, 1
  br label %loop, !llvm.loop !10
exit:
  ret i32 %i
}
!10 = distinct !{!10}
"""
    svf_output = """
==========FUNCTION: main==========
StoreStmt: [Var1 <-- Var2]\t
   store i32 %i, ptr %p, align 4 { "ln": 1, "fl": "x.c" }
8V_1 = STCHI(MR_8V_0) \tpts{1 }
"""

    oracle = adapter.build_oracle(
        ll_text=ll_text,
        svf_output=svf_output,
        loop_diagnostics=True,
    )

    loop = oracle["loop_effects"]["main\tloop"]
    assert loop["complete"] is True
    assert loop["mod_regions"] == ["MR_8"]
    assert loop["function"] == "main"
    assert loop["header"] == "loop"
    assert set(loop["blocks"]) == {"loop", "body"}
    assert oracle["diagnostics"]["loops"] == {
        "loop_count": 1,
        "complete_loop_count": 1,
        "incomplete_loop_count": 0,
    }


def test_build_oracle_records_indirect_call_targets_from_print_fp_output():
    adapter = load_adapter_module()
    ll_text = """
define dso_local i32 @f(ptr %fp, i32 %x) {
entry:
  %r = call i32 %fp(i32 %x), !dbg !12
  ret i32 %r
}
"""
    svf_output = """
==================Function Pointer Targets==================

NodeID: 44
CallSite: CallICFGNode29 {fun: f{ "ln": 5 }}
   %r = call i32 %fp(i32 %x), !dbg !12 CallICFGNode: { "ln": 5 } with Targets:
        h
        g

==========FUNCTION: f==========
CallICFGNode29 {fun: f}
   %r = call i32 %fp(i32 %x), !dbg !12 CallICFGNode: { "ln": 5 }
"""

    oracle = adapter.build_oracle(
        ll_text=ll_text,
        svf_output=svf_output,
        collect_indirect_calls=True,
    )

    assert oracle["indirect_call_targets"]["f\t%r = call i32 %fp(i32 %x)"] == {
        "targets": ["g", "h"],
        "complete": True,
    }
    assert oracle["stats"]["indirect_call_target_count"] == 1


def test_main_can_parse_saved_svf_output(tmp_path):
    adapter = load_adapter_module()
    ll = tmp_path / "input.ll"
    svf = tmp_path / "svf.txt"
    out = tmp_path / "oracle.json"
    ll.write_text(
        """
define dso_local i32 @main() {
  %2 = load i32, ptr %1, align 4
  ret i32 %2
}
"""
    )
    svf.write_text(
        """
==========FUNCTION: main==========
LDMU(MR_7V_1) \tpts{1 }
LoadStmt: [Var2 <-- Var1]\t
   %2 = load i32, ptr %1, align 4 { "ln": 1, "fl": "x.c" }
"""
    )

    rc = adapter.main(["--bc", str(ll), "--out", str(out), "--svf-output", str(svf)])

    assert rc == 0
    data = json.loads(out.read_text())
    assert data["access_regions"] == {"main\t%2 = load i32, ptr %1, align 4": ["MR_7"]}
