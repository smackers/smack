"""Unit tests for smack.pipeline.translate."""

import argparse

from smack.cli.results import VProperty
from smack.pipeline import translate
from smack.pipeline.translate import (
    llvm_to_bpl,
    memsafety_subproperty_selection,
    replace_reach_error,
)


def make_args(**overrides):
    defaults = dict(
        bpl_file=None,
        check=VProperty.NONE,
        language="c",
    )
    defaults.update(overrides)
    return argparse.Namespace(**defaults)


def make_translate_args(**overrides):
    defaults = dict(
        linked_bc_file="input.bc",
        bpl_file="output.bpl",
        warn="silent",
        sea_dsa_mode="bu",
        sea_dsa_type_aware=False,
        provenance_syms=False,
        diff_product_mode=None,
        entry_points=["main"],
        checked_functions=[],
        debug=False,
        debug_only=None,
        ll_file=None,
        mem_mod="no-reuse-impls",
        static_unroll=False,
        integer_encoding="unbounded-integer",
        timing_annotations=False,
        pointer_encoding="integer",
        no_byte_access_inference=False,
        rewrite_bitwise_ops=False,
        no_memory_splitting=False,
        memory_partitioner="sea-dsa",
        memory_partition_oracle=None,
        memory_partition_report=None,
        svf_wpa=None,
        svf_extapi=None,
        svf_mem_par=None,
        svf_analysis=None,
        svf_timeout=None,
        devirt_report=None,
        static_init_zero_memset_threshold=None,
        check=VProperty.NONE,
        fail_on_loop_exit=False,
        llvm_assumes=None,
        float=False,
        modular=False,
    )
    defaults.update(overrides)
    return argparse.Namespace(**defaults)


# --- replace_reach_error ---


def test_replace_reach_error_skips_non_svcomp(tmp_path):
    bpl = tmp_path / "t.bpl"
    body = "call reach_error();\n"
    bpl.write_text(body)
    replace_reach_error(make_args(bpl_file=str(bpl), language="c"))
    assert bpl.read_text() == body


def test_replace_reach_error_skips_memory_safety(tmp_path):
    bpl = tmp_path / "t.bpl"
    body = "call reach_error();\n"
    bpl.write_text(body)
    replace_reach_error(
        make_args(bpl_file=str(bpl), language="svcomp", check=VProperty.MEMORY_SAFETY)
    )
    assert bpl.read_text() == body


def test_replace_reach_error_skips_memleak(tmp_path):
    bpl = tmp_path / "t.bpl"
    body = "call reach_error();\n"
    bpl.write_text(body)
    replace_reach_error(make_args(bpl_file=str(bpl), language="svcomp", check=VProperty.MEMLEAK))
    assert bpl.read_text() == body


def test_replace_reach_error_skips_integer_overflow(tmp_path):
    bpl = tmp_path / "t.bpl"
    body = "call reach_error();\n"
    bpl.write_text(body)
    replace_reach_error(
        make_args(bpl_file=str(bpl), language="svcomp", check=VProperty.INTEGER_OVERFLOW)
    )
    assert bpl.read_text() == body


def test_replace_reach_error_rewrites_svcomp_assertion(tmp_path):
    bpl = tmp_path / "t.bpl"
    bpl.write_text("procedure foo() { call reach_error(); }\n")
    replace_reach_error(make_args(bpl_file=str(bpl), language="svcomp", check=VProperty.ASSERTIONS))
    assert "assert false; call reach_error();" in bpl.read_text()


# --- memsafety_subproperty_selection ---


def test_memsafety_subproperty_returns_early_if_full_memory_safety(tmp_path):
    # Should not touch the file at all when full MEMORY_SAFETY is requested.
    bpl = tmp_path / "t.bpl"
    body = "  assert {:valid_deref} a == b;\n"
    bpl.write_text(body)
    memsafety_subproperty_selection(make_args(bpl_file=str(bpl), check=VProperty.MEMORY_SAFETY))
    assert bpl.read_text() == body


def test_memsafety_subproperty_keeps_selected_attrs(tmp_path):
    bpl = tmp_path / "t.bpl"
    bpl.write_text("  assert {:valid_deref} a == b;\n")
    memsafety_subproperty_selection(make_args(bpl_file=str(bpl), check=VProperty.VALID_DEREF))
    # Original assertion kept since valid_deref is selected.
    assert "valid_deref" in bpl.read_text()
    assert "a == b" in bpl.read_text()


def test_memsafety_subproperty_replaces_unselected_with_true(tmp_path):
    bpl = tmp_path / "t.bpl"
    bpl.write_text("  assert {:valid_deref} a == b;\n")
    memsafety_subproperty_selection(make_args(bpl_file=str(bpl), check=VProperty.VALID_FREE))
    # valid_deref NOT selected — assertion body becomes `true`.
    out = bpl.read_text()
    assert "true" in out
    assert "a == b" not in out


# --- llvm_to_bpl command assembly ---


def test_llvm_to_bpl_passes_memory_partition_options(monkeypatch):
    captured = {}

    def fake_try_command(cmd, console):
        captured["cmd"] = cmd
        captured["console"] = console

    monkeypatch.setattr(translate, "try_command", fake_try_command)
    monkeypatch.setattr(translate, "annotate_bpl", lambda args: None)
    monkeypatch.setattr(translate, "memsafety_subproperty_selection", lambda args: None)
    monkeypatch.setattr(translate, "replace_reach_error", lambda args: None)
    monkeypatch.setattr(translate, "transform_bpl", lambda args: None)

    llvm_to_bpl(
        make_translate_args(
            sea_dsa_mode="butd-cs",
            sea_dsa_type_aware=True,
            memory_partitioner="svf-refined",
            memory_partition_oracle="oracle.json",
            memory_partition_report="partition.json",
            devirt_report="devirt.json",
        )
    )

    assert captured["console"] is True
    cmd = captured["cmd"]
    assert "-sea-dsa=butd-cs" in cmd
    assert "-sea-dsa-type-aware" in cmd
    assert cmd[cmd.index("-smack-memory-partitioner") + 1] == "svf-refined"
    assert cmd[cmd.index("-smack-memory-partition-oracle") + 1] == "oracle.json"
    assert cmd[cmd.index("-smack-memory-partition-report") + 1] == "partition.json"
    assert cmd[cmd.index("-smack-devirt-report") + 1] == "devirt.json"


def test_llvm_to_bpl_generates_svf_oracle_for_default_path(monkeypatch):
    captured = []
    temps = iter(["pre.ll", "generated-oracle.json"])

    def fake_try_command(cmd, console):
        captured.append((cmd, console))

    monkeypatch.setattr(translate, "temporary_file", lambda prefix, ext, args: next(temps))
    monkeypatch.setattr(translate, "try_command", fake_try_command)
    monkeypatch.setattr(translate, "annotate_bpl", lambda args: None)
    monkeypatch.setattr(translate, "memsafety_subproperty_selection", lambda args: None)
    monkeypatch.setattr(translate, "replace_reach_error", lambda args: None)
    monkeypatch.setattr(translate, "transform_bpl", lambda args: None)

    llvm_to_bpl(
        make_translate_args(
            memory_partitioner="svf-refined",
            svf_extapi="/svf/extapi.bc",
            svf_wpa="/svf/wpa",
            svf_mem_par="intra-disjoint",
            svf_timeout=12,
        )
    )

    assert len(captured) == 3
    pre_cmd, adapter_cmd, final_cmd = (entry[0] for entry in captured)
    assert "-ll" in pre_cmd
    assert pre_cmd[pre_cmd.index("-ll") + 1] == "pre.ll"
    assert "-bpl" not in pre_cmd
    assert pre_cmd[pre_cmd.index("-smack-memory-partitioner") + 1] == "sea-dsa"
    assert "-smack-skip-devirt" in pre_cmd
    assert adapter_cmd[:2] == [
        translate.sys.executable,
        str(translate._repo_root() / "tools" / "svf_memory_partition_adapter.py"),
    ]
    assert adapter_cmd[adapter_cmd.index("--bc") + 1] == "pre.ll"
    assert adapter_cmd[adapter_cmd.index("--out") + 1] == "generated-oracle.json"
    assert adapter_cmd[adapter_cmd.index("--svf-wpa") + 1] == "/svf/wpa"
    assert adapter_cmd[adapter_cmd.index("--svf-extapi") + 1] == "/svf/extapi.bc"
    assert adapter_cmd[adapter_cmd.index("--timeout") + 1] == "12"
    assert "--indirect-call-targets" in adapter_cmd
    assert final_cmd[final_cmd.index("-smack-memory-partitioner") + 1] == "svf-refined"
    assert (
        final_cmd[final_cmd.index("-smack-memory-partition-oracle") + 1]
        == "generated-oracle.json"
    )


def test_llvm_to_bpl_skips_svf_oracle_when_memory_splitting_disabled(monkeypatch):
    captured = []

    def fake_try_command(cmd, console):
        captured.append(cmd)

    monkeypatch.setattr(translate, "try_command", fake_try_command)
    monkeypatch.setattr(translate, "annotate_bpl", lambda args: None)
    monkeypatch.setattr(translate, "memsafety_subproperty_selection", lambda args: None)
    monkeypatch.setattr(translate, "replace_reach_error", lambda args: None)
    monkeypatch.setattr(translate, "transform_bpl", lambda args: None)

    llvm_to_bpl(
        make_translate_args(memory_partitioner="svf-refined", no_memory_splitting=True)
    )

    assert len(captured) == 1
    cmd = captured[0]
    assert "-no-memory-splitting" in cmd
    assert "-smack-memory-partition-oracle" not in cmd
    assert cmd[cmd.index("-smack-memory-partitioner") + 1] == "svf-refined"


def test_llvm_to_bpl_uses_inprocess_svf_native_without_oracle(monkeypatch):
    captured = []

    def fake_try_command(cmd, console):
        captured.append(cmd)

    monkeypatch.setattr(translate, "try_command", fake_try_command)
    monkeypatch.setattr(translate, "annotate_bpl", lambda args: None)
    monkeypatch.setattr(translate, "memsafety_subproperty_selection", lambda args: None)
    monkeypatch.setattr(translate, "replace_reach_error", lambda args: None)
    monkeypatch.setattr(translate, "transform_bpl", lambda args: None)

    llvm_to_bpl(
        make_translate_args(
            memory_partitioner="svf-native",
            svf_analysis="ander",
            svf_mem_par="inter-disjoint",
            svf_extapi="/svf/extapi.bc",
        )
    )

    assert len(captured) == 1
    cmd = captured[0]
    assert "-smack-memory-partition-oracle" not in cmd
    assert cmd[cmd.index("-smack-memory-partitioner") + 1] == "svf-native"
    assert cmd[cmd.index("-smack-svf-analysis") + 1] == "ander"
    assert cmd[cmd.index("-smack-svf-mem-par") + 1] == "inter-disjoint"
    assert cmd[cmd.index("-smack-svf-extapi") + 1] == "/svf/extapi.bc"
