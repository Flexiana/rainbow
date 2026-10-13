# Lean neutral exporter

Rainbow's initial foreign fixture is pinned to Lean 4.30.0, commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

The macOS ARM64 release archive used for the recorded fixture was
`lean-4.30.0-darwin_aarch64.tar.zst` with SHA-256
`072dca4a38fbc0d3cedb96fea886cc243b424f2bd16247596200b9a9ab93f0f5`.

Regenerate the neutral fixture from the repository root with the pinned `lean`
binary:

```sh
/path/to/lean-4.30.0/bin/lean foreign/lean/RainbowExport.lean
lein run -m rainbow.foreign.lean
```

The exporter inspects Lean `ConstantInfo` and `Expr` values directly. It does not
parse pretty-printed declarations or `.olean` files. The current bridge supports
bound variables, sorts, constants, applications, lambdas, dependent function
types, lets, and ordinary explicit/implicit binders. Other forms are serialized
as unsupported and must reject during Rainbow import.

## Selected Rainbow round trip

`RainbowRoundTrip.lean` is generated structurally from the checked Rainbow
declaration `logic/function-composition`. It contains no tactic script or
pretty-printed Rainbow input. Lean checks the explicit term before the same
structural `Expr` serializer emits `artifacts/day18/roundtrip-neutral.edn`, which
Rainbow imports through the ordinary pinned bridge.

Regenerate and verify the source, neutral fixture, Lean check record, and final
round-trip report with:

```sh
lein run -m rainbow.history.lean-round-trip record /path/to/lean-4.30.0/bin/lean
lein test rainbow.foreign.lean-export-test
```

Rainbow's `:theorem` kind accepts inhabitants at arbitrary sorts. Lean's
`theorem` command only accepts propositions, so this particular polymorphic
function is emitted as a Lean `def`; the return check requires its universe
parameters, type, and body to be exactly the original Rainbow structures.

## Proof-redacted Mathlib catalog

`MathlibOleanCatalog.lean` reads each compiled module's public, server, and
private `.olean` parts directly rather than estimating coverage with a
source-text regular expression. The private part preserves original theorem
kinds while every emitted value is replaced with `:redacted`.

Use a separate checkout at the pinned Mathlib `v4.30.0` commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Instantiate the dependencies from
the checked-in `lake-manifest.json` and fetch the official cache; do not run
`lake update`, because that resolves newer dependency revisions.

```sh
scripts/export-mathlib-catalog.sh /path/to/mathlib4-v4.30.0
lein run -m rainbow.history.mathlib-catalog-baseline /tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz
```

The script checks the exact Git commit and clean tracked state, partitions a
deterministic module manifest over one or two lanes, and writes through an
atomic `.partial` path. Compression is transport-only: Rainbow computes the
catalog identity over decompressed bytes during its single statistics pass.
The generated archive is local evidence and is not committed.

The compact catalog deliberately does not materialize every expanded type.
Export full proof-redacted statements only for a bounded proving stratum:

```sh
scripts/export-mathlib-statements.sh /path/to/mathlib4-v4.30.0 \
  /tmp/mathlib-function-statements.edn \
  Function.Injective.of_comp Function.LeftInverse.eq
```

This split keeps the complete denominator cheap while retaining exact statement
data wherever Rainbow is actively proving. It also amortizes Mathlib startup by
exporting a whole stroke-sized batch at once.
