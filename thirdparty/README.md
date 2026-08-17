# Third-party implementations (conformance study)

This directory vendors independently written lightweight-cipher implementations gathered from
public repositories. They are the *candidates* in the Gate-2 conformance study
(`scripts/e11_conformance.py`), each judged against our HOL-verified reference for the same cipher.

## Why vendored (not fetched at runtime)

Compute nodes are assumed to have **no internet** (`CLAUDE.md` §7). The files were fetched once and
committed here so the differential test runs identically and reproducibly offline. `MANIFEST.json`
records, for each implementation, its source URL, the cipher and variants it covers, the adapter
needed to drive it, its expected verdict, and the anonymized label used in the paper.

## Layout

- `impls/` — the vendored source files. All are unmodified from upstream except
  `xtea_marty.py`, which is a **mechanical, semantics-preserving Python-3 port** of an upstream
  Python-2 file (long-literal suffixes stripped from numeric literals, `xrange`→`range`, integer
  division fixed; cipher logic and struct format strings unchanged). Its header documents the exact
  changes, and `e11` validates faithfulness by reproducing the official XTEA test vectors.
- `MANIFEST.json` — provenance + adapter registry consumed by the harness.

## Adapter kinds (see `src/corpus/conformance.py`)

Each implementation exposes a different interface; the manifest names the adapter that normalizes it
to `encrypt(pt:int, key:int) -> int`:

- `class_ss`  — `Cls(key, key_size=k, block_size=b).encrypt(pt)` (inmcm Simon/Speck, multi-variant)
- `class_int` — `Cls(key).encrypt(pt)`
- `class_bytes` — `Cls(key_bytes).encrypt(pt_bytes)`, big-endian
- `func_int`  — `entry(pt, key)`
- `func_hex`  — `entry(pt_hex, key_hex)` returning a hex string

Two compatibility shims are applied at load time (never to the verified reference): `xrange` is
bound to `range` for Python-2 sources, and the legacy `Padding` module is stubbed (it is used only
by demo code, never by block encryption).

## License

These are third-party files retained for evaluation and reproducibility only. **Verify each
project's license before any public redistribution** of this directory.
