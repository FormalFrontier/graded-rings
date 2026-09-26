# Native API documentation

[`API.md`](API.md) contains the 104 public declarations of the nine production
leaves. All 28 shipped modules are included: the aggregate, fourteen tests and
four examples introduce no additional public declarations. Display signatures
retain every native header token, including implicit hypotheses; they are not
proof bodies or standalone declarations. Existing module comments and declaration
docstrings are preserved. The 39 absent declaration docstrings are explicitly
identified; the adapter does not fabricate their text.

## Reproduction

The [manifest](api-manifest.json) binds all 28 Lean inputs, Lake configuration,
toolchain and dependency manifest, the native records and rendered Markdown.
The [inventory](../scripts/api-inventory.json) freezes module-to-source mappings,
public declaration names/kinds/origins, display kinds and docstring availability.
Test and example module names are flat: `Axioms` comes from `test/Axioms.lean`,
not `Axioms.lean`; `Symmetric` comes from `examples/Symmetric.lean`.

Build the separate core-only doc-gen4 tool at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, using its committed manifest and
Lean `v4.34.0-rc2`, with `lake build doc-gen4`. Do not change this library's
dependencies. In the library checkout, fetch matching mathlib artifacts before
building all default targets, as described in the [root README](../README.md).
Use an exact full analyzed revision whose source/config bytes equal this checkout.

The following Python recipe invokes native doc-gen4 for the explicit inventory.
Replace the three placeholders. Choose fresh output paths; existing directories
are refused. Run from the library root in the pinned Lake environment.

```python
import json
from pathlib import Path
import subprocess

tool = "/absolute/path/to/doc-gen4"
revision = "FULL_ANALYZED_SOURCE_COMMIT"
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

Omit `--check` only when intentionally generating an updated reference. Run
`python3 -B scripts/test_generate_api.py` for the synthetic data controls.

When the analyzed commit is present, the adapter compares every source/config
byte with that Git object. When development history is intentionally absent from
a parentless release, the reproduced manifest must instead equal the committed
release manifest, and every source/config input must equal its committed file.
A present but incorrect object, drifted input, or changed/uncommitted manifest is
refused. Use a Git checkout; a plain file export is not this verification mode.
The development identifier in native records need not resolve on a public host.
Distributed source links are relative to the checkout.

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
