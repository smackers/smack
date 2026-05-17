from __future__ import annotations

import json

from smack.diffprod.llvm_match import build_llvm_match, parse_llvm_ir
from smack.diffprod.pipeline import build_from_bpl

LEFT_LL = """
define i32 @f(i32 %x) {
entry:
  %a = add i32 %x, 0
  br label %hot
hot:
  %b = mul i32 %a, 1
  ret i32 %b
}
"""


RIGHT_LL = """
define i32 @f(i32 %x) {
entry:
  %a = add i32 %x, 0
  br label %hot
hot:
  %b = add i32 %a, 0
  ret i32 %b
}
"""


LEFT_BPL = """
procedure f(x: int) returns (r: int);
implementation f(x: int) returns (r: int)
{
  var a: int;

entry:
  assume {:llvm.func "f"} {:llvm.bb "entry"} {:llvm.inst "f:entry:0"} {:llvm.op "add"} true;
  a := x + 0;
  goto hot;

hot:
  assume {:llvm.func "f"} {:llvm.bb "hot"} {:llvm.inst "f:hot:0"} {:llvm.op "mul"} true;
  r := a * 1;
  return;
}
"""


RIGHT_BPL = """
procedure f(x: int) returns (r: int);
implementation f(x: int) returns (r: int)
{
  var a: int;

entry:
  assume {:llvm.func "f"} {:llvm.bb "entry"} {:llvm.inst "f:entry:0"} {:llvm.op "add"} true;
  a := x + 0;
  goto hot;

hot:
  assume {:llvm.func "f"} {:llvm.bb "hot"} {:llvm.inst "f:hot:0"} {:llvm.op "add"} true;
  r := a + 0;
  return;
}
"""


def test_llvm_matcher_classifies_stable_and_changed_blocks():
    parsed = parse_llvm_ir(LEFT_LL)
    assert sorted(parsed.functions) == ["f"]
    assert [block.label for block in parsed.functions["f"].blocks] == ["entry", "hot"]

    match = build_llvm_match(
        left_ll=LEFT_LL,
        right_ll=RIGHT_LL,
        left_entry="f",
        right_entry="f",
    )

    by_block = {
        chunk["left"]["block"]: chunk for chunk in match["chunks"] if chunk["left"] is not None
    }
    assert by_block["entry"]["kind"] == "stable"
    assert by_block["hot"]["kind"] in {"similar", "changed"}
    assert match["stats"]["stable"] == 1
    json.dumps(match)


def test_llvm_matcher_metadata_seeds_boogie_product_delta():
    match = build_llvm_match(
        left_ll=LEFT_LL,
        right_ll=RIGHT_LL,
        left_entry="f",
        right_entry="f",
    )
    result = build_from_bpl(
        left_bpl=LEFT_BPL,
        right_bpl=RIGHT_BPL,
        diff_text="",
        left_entry="f",
        right_entry="f",
        alignment="legacy",
        llvm_match=match,
    )

    report = result.to_json()
    assert report["llvm_match"]["stats"]["stable"] == 1
    assert "proc:f:block:hot" in result.impact.left.impacted_blocks
    assert "proc:f:block:entry" not in result.impact.left.impacted_blocks
    assert report["product"]["delta"]["left_blocks"] == ["hot"]
    assert report["product"]["delta"]["right_blocks"] == ["hot"]
    assert not any(
        "whole-program structural region" in diagnostic for diagnostic in report["diagnostics"]
    )
