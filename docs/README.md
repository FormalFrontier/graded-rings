# API documentation and historical native snapshot

[`API.md`](API.md) is the **hand-maintained current** ten-leaf module/API map,
not a fresh native display or a complete declaration census. The
[degree-multiplying map guide](degree-multiplying-homogeneous-localization.md)
explains all thirteen new entry points, precise hypotheses and clients.

[`API-initial-snapshot.md`](API-initial-snapshot.md) is byte-for-byte the native
doc-gen4 output for the original nine production leaves: 104 exposed
declarations across the former 28-module checkout (nine leaves, one aggregate,
fourteen tests and four examples). This historical display retains every
native header token, including implicit hypotheses; it is neither proof bodies
nor standalone declarations. Existing module comments and docstrings were
preserved; the 39 absent declaration docstrings were identified rather than
fabricated. Its source links and line positions reflect the original checkout,
not necessarily the expanded current source files.

## Reproduction

The unchanged [manifest](api-manifest.json) binds the original 28 Lean inputs,
Lake configuration, toolchain, dependency manifest, native records and archived
Markdown. Its `api_sha256` is
`ac5651103124211c0274f9068b4367af2d0860aea482456a17ba5692f3b1e70d`,
the digest of **`API-initial-snapshot.md`**, not of current `API.md`.
The unchanged [inventory](../scripts/api-inventory.json) freezes the old
module-to-source mappings, declaration names/kinds/origins, display kinds and
docstring availability. The old generator and controls
([`generate_api.py`](../scripts/generate_api.py),
[`test_generate_api.py`](../scripts/test_generate_api.py)) apply only to this
original inventory. In particular, their old source/root/Lakefile hashes
cannot check the enlarged current tree; passing old synthetic controls does
not check its API or proofs.
Test and example module names are flat: `Axioms` comes from `test/Axioms.lean`,
not `Axioms.lean`; `Symmetric` comes from `examples/Symmetric.lean`.

For historical reproduction use a **separate checkout** at exact initial
official revision `acbdc8381a0d50b37791a40c71c09d4b5d213559` (same tree
as original accepted internal `1ccc70792c15889b031f2d3c7566d15732354ef3`),
or the exact analyzed-input revision
`497babfcb2a4d0a016722416ebaeb50a234c51a0`. Do not run the historical
adapter's `--check` or output mode on the expanded current checkout; its
original inventory and changed `GradedRings.lean`, `test/RootClient.lean` and
`lakefile.toml` inputs no longer match. The archive's input hashes and links
refer to that original 2026-09-27 official release and analyzed revision.

Build the separate core-only doc-gen4 tool at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, using its committed manifest and
Lean `v4.34.0-rc2`, with `lake build doc-gen4`. Do not change this library's
dependencies. In that **historical** library checkout, fetch matching mathlib
artifacts before building all default targets, as described in the
[root README](../README.md). The procedure below records original reproduction
instructions only; no new native documentation run is asserted here.

The following Python recipe invokes native doc-gen4 for the explicit inventory.
Replace the tool and output-directory placeholders. Choose fresh output paths; existing directories
are refused. Run from the library root in the pinned Lake environment.

```python
import json
from pathlib import Path
import subprocess

tool = "/absolute/path/to/doc-gen4"
revision = "497babfcb2a4d0a016722416ebaeb50a234c51a0"
work = Path("/absolute/path/to/fresh-output-directory")
analysis, render = work / "analysis", work / "render"
analysis.mkdir(parents=True, exist_ok=False)
render.mkdir(exist_ok=False)
modules = json.loads(Path("scripts/api-inventory.json").read_text())["modules"]
for module, source in modules.items():
    uri = "https://github.com/FormalFrontier/graded-rings/blob/" + revision + "/" + source
    subprocess.run(["lake", "env", tool, "single", "--build", str(analysis),
                    module, "api.db", uri], check=True)
subprocess.run(["lake", "env", tool, "bibPrepass", "--build", str(render), "--none"], check=True)
subprocess.run(["lake", "env", tool, "fromDb", "--build", str(render),
                "--manifest", str(render / "manifest.json"), str(analysis / "api.db")], check=True)
subprocess.run(["python3", "-B", "scripts/generate_api.py", "--native-data",
                str(render / "doc-data"), "--source-revision", revision, "--check"], check=True)
```

The original checkout has `docs/API.md` with exactly the archived bytes, so
its `--check` mode can compare the historical rendered output. Run
`python3 -B scripts/test_generate_api.py` for the old synthetic data controls.
This recipe does not regenerate or certify the expanded API map.

When the analyzed commit is present, the adapter compares every source/config
byte with that Git object. When development history is intentionally absent from
a parentless release, the reproduced manifest must instead equal the committed
release manifest, and every source/config input must equal its committed file.
A present but incorrect object, drifted input, or changed/uncommitted manifest is
refused. Use a Git checkout; a plain file export is not this verification mode.
The development identifier in native records need not resolve on a public host.
Archived source links are relative to the historical checkout and their old
line numbers may be stale in this version.

## Limits and provenance

The purpose-specific adapter refuses wrong module/name/kind inventories, malformed
header markup, unsafe/partial kind substitutions, stale links, invalid source
ranges and mismatched source bindings. It handles the simple module-comment
envelopes used here, not arbitrary Lean syntax. Data controls and hash equality
do not authenticate the native execution, verify mathematical proofs, clear
rights, or grant release acceptance. Those require separate exact-artifact review.

Only Markdown, the input manifest and the small adapter/controls are shipped.
Intermediate HTML, SQLite, dependency websites, fonts and JavaScript are excluded.
Lean, mathlib and doc-gen4 retain their own authorship and licensing.

Atlas adapted the renderer and controls from multivariate-polynomials
`6b72818d5fe42923852c7be99e9377007ae037ed`, continuing the toric-ideals,
minimal-primes and integral-closure recipes and Anchor's original ideal-completion
recipe `f0c8c34386109116e4912fb425a8ad15d9dc42a4`. Formal Frontier collective
credit and Apache-2.0 terms are retained; prior approval does not transfer.
The mathematical inputs retain their [own provenance](PROVENANCE.md).
