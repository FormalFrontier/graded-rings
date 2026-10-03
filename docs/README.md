# Documentation and API references

[`API.md`](API.md) is the **current, hand-maintained 25-production-leaf map**:
it links the available modules and selected interfaces. It is not a native
declaration census or a proof certificate. Import `GradedRings` for the full
public API, or ordinary-import a subject leaf. The [root README](../README.md)
provides the headline mathematics, limitations and cache-first build commands.

## Subject guides

- **Quotients and localization:** [degree-multiplying homogeneous-localization
  maps](degree-multiplying-homogeneous-localization.md) complement the
  [quotient](../GradedRings/Quotient.lean) and
  [same-ring localization](../GradedRings/Localization.lean) modules.
- **Polynomial constructions:** [homogeneous lifts](HomogeneousLifts.md) and
  [weighted evaluation](WeightedEvaluation.md) distinguish grading preservation
  from the extra algebra-generation premise needed to lift every component.
- **Selected rings:** [Veronese construction](Veronese.md), [all-index degree
  zero](VeroneseZero.md), [positive degree-one generation](VeroneseDegreeOne.md),
  [finite degree-one generation](FiniteVeronese.md), [finite type at each
  prescribed positive index](VeroneseFiniteType.md), and
  [coherent high tails](CoherentTailVeronese.md) state separate hypotheses.
- **Weighted polynomials:** [positive-weight exponent blocks](WeightedBlocks.md),
  [monomial-adjoin membership](WeightedBlockAdjoin.md) and
  [selected weighted-polynomial generators](WeightedVeroneseGenerators.md)
  describe different combinatorial and polynomial results.
- **Finiteness and residues:** [finite positive-index inclusion](VeroneseFinite.md),
  [whole-ring linear residue projection](VeroneseResidue.md) and
  [external shifted residue sums](VeroneseResidueModule.md) distinguish
  finiteness of the old ring, a particular projection range and the shifted sum.

The guides document the current mathematical API, clients, code hypotheses
and limits; they do not assert source completeness.

## Historical native snapshot

[`API-initial-snapshot.md`](API-initial-snapshot.md) is the byte-exact original
native doc-gen4 Markdown for **104 public declarations in nine original
production leaves**, from an earlier **28-module** tree (one aggregate,
fourteen tests and four examples). The original inventory records 39 missing
docstrings and `proof_certification: false`. Its relative source links and
source line ranges refer to that historical tree, **not necessarily the
current checkout**. To follow an old link accurately, open the [exact
historical public checkout](https://github.com/FormalFrontier/graded-rings/tree/acbdc8381a0d50b37791a40c71c09d4b5d213559)
and its [original public API document](https://github.com/FormalFrontier/graded-rings/blob/acbdc8381a0d50b37791a40c71c09d4b5d213559/docs/API.md).
The Markdown here has the same bytes as that original `docs/API.md`; neither
the snapshot nor its old line ranges describe newly added modules. The native
analyzed revision `497babfcb2a4d0a016722416ebaeb50a234c51a0` is a
**technical verification binding**, not a promised public GitHub object or
a separate release-acceptance decision.

## Reproducing the original snapshot

The unchanged [manifest](api-manifest.json) binds 31 original source/config
input hashes (28 Lean modules plus Lake configuration/toolchain/manifest),
native records and the archived Markdown. Its `api_sha256` is
`ac5651103124211c0274f9068b4367af2d0860aea482456a17ba5692f3b1e70d`,
the SHA-256 of **`API-initial-snapshot.md`**, not current `API.md`. The
unchanged [inventory](../scripts/api-inventory.json) freezes the old
module-to-source mapping, declaration names/kinds/origins and docstring
availability. The [old adapter](../scripts/generate_api.py) and
[synthetic controls](../scripts/test_generate_api.py) apply only there.

Use a **separate Git checkout at official public revision**
`acbdc8381a0d50b37791a40c71c09d4b5d213559` (the same tree as the
original accepted internal `1ccc70792c15889b031f2d3c7566d15732354ef3`),
or the exact analyzed-input revision
`497babfcb2a4d0a016722416ebaeb50a234c51a0` if locally available.
Do not run this historical adapter's output mode or `--check` on the
expanded current checkout: `GradedRings.lean`, `test/RootClient.lean` and
`lakefile.toml` no longer match the original inputs, and the current
`docs/API.md` is a different manual map. Only the separate **original**
checkout has `docs/API.md` containing the archived output that `--check`
compares. Flat module names include `Axioms` from `test/Axioms.lean` and
`Symmetric` from `examples/Symmetric.lean`.

In the original checkout, use its pinned Lean `v4.34.0-rc2` and committed
manifest; **successfully fetch the matching mathlib cache before building**
its default targets. Build the separate core-only doc-gen4 tool at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db` under its own pinned
manifest with `lake build doc-gen4` (cache-first if it depends on mathlib).
Do not change this library's dependencies. This historical reproduction
recipe is guidance, not a claim that a new native documentation run occurred:

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

The `revision` in this recipe reproduces the original manifest's **technical
binding** and native data, not a navigable public source URL. Use the
separate official public checkout/API links above for public navigation.
`python3 -B scripts/test_generate_api.py` runs the old synthetic controls
but does not check the expanded current API or proofs.

If the analyzed Git commit exists locally, the adapter checks every recorded
source/config byte against that Git object. If its development history is
intentionally absent from a parentless official release, the reproduced
manifest must equal the committed release manifest and every source/config
input must equal its committed file. A present incorrect object, drifted
input, or changed/uncommitted manifest is **rejected**; a plain file export
does not provide the required Git checkout. The old native display's relative
source ranges are historical. The adapter also refuses wrong module/name/kind
inventories, malformed markup, partial/unsafe substitutions, stale links,
invalid ranges and mismatched bindings. Its simple module-comment handling
is not a general Lean parser.

The snapshot and checks do not authenticate native execution, certify proofs,
clear rights or grant release acceptance. Only Markdown, the input manifest
and small adapter/controls are shipped, not HTML/SQLite/dependency sites or
assets. Lean, mathlib and doc-gen4 retain their own authorship and terms;
see [project provenance and credits](PROVENANCE.md).
