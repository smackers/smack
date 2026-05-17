#!/usr/bin/env python3
"""Build a local BearSSL checkout into linked LLVM bitcode for devirt benchmarks."""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
from pathlib import Path


class BuildError(RuntimeError):
    """Raised when BearSSL bitcode cannot be produced."""


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def resolve_tool(value: str | None, name: str, *, repo_root: Path) -> Path:
    candidates: list[Path]
    if value:
        path = Path(value)
        candidates = [path]
        if not path.is_absolute():
            candidates.insert(0, repo_root / path)
    else:
        candidates = [
            repo_root / "build-llvm22c" / name,
            Path(name),
            Path("/usr/lib/llvm-22/bin") / name,
        ]

    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()

    if value is None:
        found = shutil.which(name)
        if found:
            return Path(found).resolve()

    raise BuildError(f"required tool not found: {value or name}")


def run_command(args: list[str], *, cwd: Path, timeout: int) -> None:
    try:
        completed = subprocess.run(
            args,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        raise BuildError(f"command timed out: {' '.join(args)}\n{output}") from exc

    if completed.returncode != 0:
        raise BuildError(
            "command failed with exit code "
            f"{completed.returncode}: {' '.join(args)}\n{completed.stdout}"
        )


def default_driver_source() -> str:
    return r'''
#include <stddef.h>
#include <stdint.h>

#include "bearssl.h"

static unsigned char iobuf[BR_SSL_BUFSIZE_BIDI];

typedef union {
  const br_block_cbcenc_class *vtable;
  br_aes_big_cbcenc_keys big;
  br_aes_small_cbcenc_keys small;
  br_aes_ct_cbcenc_keys ct;
  br_aes_ct64_cbcenc_keys ct64;
} bearssl_cbcenc_any;

typedef union {
  const br_block_ctr_class *vtable;
  br_aes_big_ctr_keys big;
  br_aes_small_ctr_keys small;
  br_aes_ct_ctr_keys ct;
  br_aes_ct64_ctr_keys ct64;
} bearssl_ctr_any;

static const br_hash_class *select_hash(unsigned selector) {
  switch (selector & 3U) {
  case 0:
    return &br_sha1_vtable;
  case 1:
    return &br_sha256_vtable;
  case 2:
    return &br_sha512_vtable;
  default:
    return &br_md5sha1_vtable;
  }
}

static const br_block_cbcenc_class *select_cbcenc(unsigned selector) {
  switch (selector & 3U) {
  case 0:
    return &br_aes_big_cbcenc_vtable;
  case 1:
    return &br_aes_small_cbcenc_vtable;
  case 2:
    return &br_aes_ct_cbcenc_vtable;
  default:
    return &br_aes_ct64_cbcenc_vtable;
  }
}

static const br_block_ctr_class *select_ctr(unsigned selector) {
  switch (selector & 3U) {
  case 0:
    return &br_aes_big_ctr_vtable;
  case 1:
    return &br_aes_small_ctr_vtable;
  case 2:
    return &br_aes_ct_ctr_vtable;
  default:
    return &br_aes_ct64_ctr_vtable;
  }
}

int bearssl_devirt_hash_entry(const unsigned char *input, size_t len) {
  unsigned char digest[64];
  unsigned char state[64];
  br_hash_compat_context hc;
  const br_hash_class *hash = select_hash(input ? input[0] : 0);

  hash->init(&hc.vtable);
  hash->update(&hc.vtable, input, len);
  hash->out(&hc.vtable, digest);
  return (int)(hash->state(&hc.vtable, state) ^ digest[0]);
}

int bearssl_devirt_block_entry(const unsigned char *input, size_t len) {
  static const unsigned char key[16] = {0};
  unsigned char iv[16] = {0};
  unsigned char nonce[12] = {0};
  unsigned char block[32] = {0};
  bearssl_cbcenc_any cbc;
  bearssl_ctr_any ctr;
  const br_block_cbcenc_class *cbc_impl =
      select_cbcenc(input ? input[0] : 0);
  const br_block_ctr_class *ctr_impl =
      select_ctr(input && len > 1 ? input[1] : 0);

  cbc_impl->init(&cbc.vtable, key, sizeof key);
  cbc_impl->run(&cbc.vtable, iv, block, 16);
  ctr_impl->init(&ctr.vtable, key, sizeof key);
  return (int)ctr_impl->run(&ctr.vtable, nonce, 1, block, sizeof block);
}

int bearssl_devirt_ssl_entry(const unsigned char *input, size_t len) {
  br_ssl_client_context sc;
  br_x509_minimal_context xc;

  br_ssl_client_init_full(&sc, &xc, 0, 0);
  br_ssl_engine_set_buffer(&sc.eng, iobuf, sizeof iobuf, 1);
  if (!br_ssl_client_reset(&sc, "example.com", 0)) {
    return -1;
  }
  return br_ssl_engine_current_state(&sc.eng) ^ (int)(len + (input ? input[0] : 0));
}

int bearssl_devirt_entry(const unsigned char *input, size_t len) {
  return bearssl_devirt_hash_entry(input, len) ^
      bearssl_devirt_block_entry(input, len) ^
      bearssl_devirt_ssl_entry(input, len);
}
'''.lstrip()


def collect_bearssl_sources(source_root: Path) -> list[Path]:
    src_dir = source_root / "src"
    include = source_root / "inc" / "bearssl.h"
    if not src_dir.is_dir() or not include.is_file():
        raise BuildError(f"not a BearSSL source checkout: {source_root}")

    sources = sorted(path for path in src_dir.rglob("*.c") if path.is_file())
    if not sources:
        raise BuildError(f"no BearSSL C sources found under {src_dir}")
    return sources


def object_name(source: Path, *, source_root: Path) -> str:
    relative = source.relative_to(source_root).as_posix()
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", relative) + ".bc"


def build_bearssl_bitcode(
    *,
    source_root: Path,
    out_dir: Path,
    clang: Path,
    llvm_link: Path,
    cflags: list[str],
    driver: Path | None,
    output: Path,
    timeout: int,
) -> Path:
    source_root = source_root.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    obj_dir = out_dir / "objects"
    obj_dir.mkdir(parents=True, exist_ok=True)

    smack_include = _repo_root() / "share" / "smack" / "include"
    include_flags = [
        f"-I{source_root / 'inc'}",
        f"-I{source_root / 'src'}",
        f"-I{smack_include}",
    ]
    compat_flags = [
        "-Wno-incompatible-pointer-types",
        "-Wno-deprecated-non-prototype",
        "-Wno-implicit-function-declaration",
        "-Wno-int-conversion",
    ]
    common = ["-O0", "-g", "-emit-llvm", "-c", *include_flags, *compat_flags, *cflags]

    objects: list[Path] = []
    for source in collect_bearssl_sources(source_root):
        bc = obj_dir / object_name(source, source_root=source_root)
        run_command([str(clang), *common, str(source), "-o", str(bc)], cwd=source_root, timeout=timeout)
        objects.append(bc)

    if driver is None:
        driver = out_dir / "bearssl_devirt_driver.c"
        driver.write_text(default_driver_source())
    elif not driver.exists():
        raise BuildError(f"BearSSL driver source not found: {driver}")

    driver_bc = obj_dir / "bearssl_devirt_driver.bc"
    run_command([str(clang), *common, str(driver), "-o", str(driver_bc)], cwd=source_root, timeout=timeout)
    objects.append(driver_bc)

    run_command([str(llvm_link), *[str(obj) for obj in objects], "-o", str(output)], cwd=source_root, timeout=timeout)
    return output


def make_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=_repo_root())
    parser.add_argument("--bearssl-source", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, default=Path("build/devirt-bearssl"))
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--clang")
    parser.add_argument("--llvm-link")
    parser.add_argument("--driver", type=Path, default=None)
    parser.add_argument("--cflag", action="append", default=[], help="extra C flag; may be repeated")
    parser.add_argument("--timeout", type=int, default=300)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = make_arg_parser()
    args = parser.parse_args(argv)
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    output = args.output or (out_dir / "bearssl-linked.bc")
    if not output.is_absolute():
        output = repo_root / output

    try:
        clang = resolve_tool(args.clang, "clang", repo_root=repo_root)
        llvm_link = resolve_tool(args.llvm_link, "llvm-link", repo_root=repo_root)
        built = build_bearssl_bitcode(
            source_root=args.bearssl_source,
            out_dir=out_dir,
            clang=clang,
            llvm_link=llvm_link,
            cflags=list(args.cflag or []),
            driver=args.driver,
            output=output,
            timeout=args.timeout,
        )
    except BuildError as exc:
        parser.error(str(exc))

    print(built)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
