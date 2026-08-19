# CipherGuard 

**Reference-free detection of test-vector–passing cryptographic backdoors in lightweight block-cipher implementations, via the data-oblivious invariant.**


CipherGuard decides whether an untrusted cipher implementation has been **backdoored** — including
a backdoor crafted to still pass the published test vectors — **without a trusted reference and
without cryptanalysis**. It checks a structural invariant that clean lightweight ciphers satisfy on
their encryption path and that a useful backdoor must violate.

---

## 1. The idea in one paragraph

A clean lightweight block cipher's `encrypt` routine has control flow that does **not** depend on
plaintext/key *values*, and it routes the key to the output only through the key schedule. A
backdoor useful to an attacker must, on the encryption path, either **trigger** on a
secret-dependent condition or **route the key to the output** along a shortcut that bypasses the
round function — either injects secret-dependent structure a clean cipher never has, so it is
detectable **reference-free**. CipherGuard's primary detector (**L1**) checks both, interprocedurally,
so it also catches a **branchless** key leak (which a constant-time analyzer passes) and a
helper-hidden leak. A second reference-free layer (**L2**) executes the implementation and measures
cryptographic properties (diffusion, avalanche, an affine-relation test), catching **weakenings**
such as a substituted weak S-box. The one class L1 cannot catch reference-free — a backdoor confined
to the key schedule — is a *characterized* boundary, not a silent gap.

The graphs and the interpretable check are built from the implementation's **source** (Python
`ast`); Isabelle/HOL is used only **offline** to build the verified corpus and never at detection
time.

---

## 2. Requirements

- **Everything except the learned GAT baseline: Python 3.9+ and `numpy` only.** No GPU, no internet,
  no Isabelle needed at runtime (third-party implementations for the conformance study are vendored
  under `thirdparty/`; the corpus verification is done offline once).
- **Optional GAT baseline (RQ4):** `torch` + `torch_geometric` on Python 3.10–3.12 (see
  `requirements-train.txt`). CPU is sufficient.

```bash
python3 -c "import numpy"           # all you need for the pipeline and e6–e14
# optional GAT baseline only:
pip install torch --index-url https://download.pytorch.org/whl/cpu
pip install torch_geometric numpy
```

---

## 3. How to run

Each stage derives paths from the repo root, logs `[CipherGuard][<stage>][CKPT k/N] …`
checkpoints (console + `logs/`), fails loudly on integrity errors, and writes machine-readable
outputs. Everything is deterministic (fixed seeds).

```bash
# reproduce every interpretable-check experiment at once (numpy only, offline):
bash scripts/run_experiments.sh          # builds the dataset (stages 00–03) then runs e6–e14

# or run the pipeline / experiments individually:
python3 scripts/00_corpus.py             # parse verified theories -> datasets/registry/
python3 scripts/01_inject.py             # inject T0–T6 + backdoor styles -> datasets/{tampered,items}/
python3 scripts/02_extract.py            # source -> firewall-safe graphs -> datasets/graphs/source/
python3 scripts/03_dataset.py            # master index + leakage-free splits -> datasets/splits/

# experiments, mapped to the paper's research questions:
python3 scripts/e9_behavioral_baselines.py   # RQ1  vs fuzzing / avalanche (rare-trigger backdoors)
python3 scripts/e6_backdoor_styles.py        # RQ2  per-style robustness
python3 scripts/e10_harder_backdoors.py      # RQ2  helper-hidden adaptive backdoors (S7/S8)
python3 scripts/e13_adaptive_evasion.py      # RQ2  adaptive evasions A1/A3 + hardening (before/after)
python3 scripts/e7_graphedit_baseline.py     # RQ3  "why not diff a reference?" (Regime A vs B)
python3 scripts/e8_ct_vs_cipherguard.py      # RQ5  vs a constant-time analyzer (branchless leak)
python3 scripts/e12_property_probes.py       # RQ6  L2 property probes (weakenings) + clean FPR
python3 scripts/e14_literature_weakenings.py # RQ6  L2 vs literature weak S-boxes (non-circular)
python3 scripts/e11_conformance.py           # RQ7  conformance vs real third-party implementations

# optional learned GAT baseline (RQ4; needs torch/PyG):
bash scripts/run_local.sh
```

Outputs land in `datasets/`, `results/`, `reports/`, and `logs/` (created on first run).

---

## 4. What's here

```
src/
  common/     paths, checkpoint logging, seeding, JSON IO
  corpus/     theory parser -> registry; verification; conformance oracle (e11); property probes (L2, e12)
  tamper/     tamper taxonomy (T0–T6), source-AST injectors, executable oracle, backdoor styles (S1–S8)
  extraction/ source -> firewall-safe structural graph (Python ast), design vector, localization
  models/     the detector (constant-time baseline + interprocedural invariant check) and learned baselines
  dataset/    dataset assembly, labels, leakage-free splits
  evaluation/ metrics, aggregation
scripts/      pipeline stages 00–05 + experiments e6–e14 + run_experiments.sh / run_local.sh / run_cluster.sh
spike_t6/cipher_lib/   INPUT: executable Python reference implementations (the clean ciphers)
new-dataset-thy-ciphers/  INPUT: Isabelle/HOL cipher theories (the kernel-verified corpus)
thirdparty/   INPUT: vendored third-party cipher implementations + MANIFEST for the conformance study (e11)
requirements-train.txt    dependencies for the optional GAT baseline
```

---

## 5. Dataset

- **Corpus:** 44 formally verified block ciphers across Feistel, ARX, and SPN families (SIMON, SPECK,
  SIMECK, PRESENT, GIFT, SKINNY, RECTANGLE, LEA, XTEA, HIGHT, CHAM, SPARX, …), each kernel-verified in
  Isabelle/HOL (test vectors + invertibility proven).
- **Objective labels:** we *inject* the tampering, so labels are objective by construction. The
  taxonomy is T0 (clean) and T1–T6; the backdoor class (T6) is realized through six structurally
  distinct styles plus two adaptive, detector-aware variants. Every injected backdoor is verified by
  an executable oracle to (a) preserve the test vector and (b) be exploitable.
- **414 labeled implementations**, with leakage-free splits (by variant; held-out backdoor type;
  held-out family).

---

## 6. Key results (all produced by the scripts above)

| Question | Result |
|---|---|
| Catch test-vector–passing backdoors? | Formal checks (KAT, invertibility) = **0** by construction; behavioral testing also misses them (fuzzing needs ~10⁵–10⁶ tests for a 2⁻¹⁶ trigger, useless at 2⁻³²; avalanche = 0). CipherGuard = **1.0**, independent of trigger rarity. |
| Robust across backdoor styles? | **1.0** on all encryption-path styles, **0.0 FPR** on 44 clean ciphers. Two further adaptive evasions we constructed are closed by a hardened check at zero regression (`e13`). |
| Just constant-time analysis? | No — a control-flow CT analyzer misses the **branchless leak**; L1 catches it via a data-flow signal. |
| Weakenings (L2)? | S-box weakening **10/10**, nonlinearity removal **12/38**, round reduction **0/40** (disclosed boundary), **0/44 clean FPR**. |
| Real third-party code? | The verified corpus doubles as a conformance oracle: reproduces 9 official vectors across 4 ciphers, agrees with 6 independent implementations on ~24k inputs, flags one non-conforming PRESENT (`e11`). |
| Why not just diff a reference? | With the exact reference (Regime A) a graph diff catches everything; without it (Regime B) a nearest-clean diff is **AUROC 0.524 — chance**. |
| Boundary | A backdoor confined to the **key schedule** is not reliably detectable reference-free — a principled limitation, addressed by a complementary behavioral weak-key probe. |

---

## 7. Reproducibility notes

- **Determinism:** all stages set a fixed seed; outputs are stable across runs.
- **No network / no prover at runtime.** The Isabelle verification of the corpus is offline and
  one-time; the runtime detector consumes source structure only. On a machine without Isabelle,
  `00_corpus.py` records a portable behavioral cross-check instead — this does not affect detection.
- **Self-contained:** the executable cipher models live in `spike_t6/cipher_lib/`; the third-party
  implementations for the conformance study are vendored in `thirdparty/`. Nothing is fetched at
  runtime.
- **Paths:** every script derives the repo root from its own location; run from anywhere.
