# Prime Algorithm — v0.1-verified

Final Lean 4 proofs of exact prime summation, exact prime counting, and
deterministic prime finding, together with the announcement and verification
evidence. This repository contains the source dependency closure of these three
results. Exploratory experiments and intermediate research notes are omitted.

The proofs use the pinned counting engine of Anthropic and the bridge library
of Vaibhav Tulsyan. The bounds are asymptotic; this is not a practical prime
computation program. See [the announcement](paper/primes-note.pdf).

## The three statements

Read [MainResults.lean](formal/independent/PrimeIndependent/MainResults.lean)
first. It imports only Mathlib and specifies:

| Endpoint | Output |
| --- | --- |
| `PrimeIndependent.primeSum_time` | Exact sum of all primes at most `N` |
| `PrimeIndependent.primeCounting_time` | Mathlib's `Nat.primeCounting N` |
| `PrimeIndependent.primeFinding_time` | A prime `p` with `N < p ≤ 2 * max N 1` |

Each statement chooses one finite-alphabet deterministic Turing machine and one
constant before quantifying over every natural input, including zero and one.
With `b = (Nat.bits N).length`, the complete execution bound is
`floor(C * 2^(C*b/sqrt(log₂(b+2))))`.

[Solution.lean](formal/independent/PrimeIndependent/Solution.lean) proves these
specifications. The three `sorry` declarations in `Challenge.lean` are the
statement-only inputs to Comparator. They are excluded from Solution's import
closure. The proved endpoints depend only on `propext`, `Classical.choice`,
and `Quot.sound`.

## Build from a fresh clone

Prerequisites: Git, Python 3.9 or newer, a C compiler, and
[elan](https://lean-lang.org/install/). On macOS, install the Xcode Command Line
Tools. Initial setup needs network access and substantial free disk space for
Lean, Mathlib, and their build outputs.

```sh
git clone https://github.com/6teamFurina/prime-algorithm.git
cd prime-algorithm
python3 scripts/bootstrap.py --cache
python3 scripts/verify.py
```

Authentication is required while this repository is private. Bootstrap installs
Lean **4.33.1** into this checkout, fetches every source at the revisions in
[dependencies.lock.json](dependencies.lock.json), assembles the upstream engine,
and registers all three independent specifications and their proofs. `--cache`
allows the official pinned Mathlib cache for this ordinary build. Omit it to
build dependencies from source.

The final build and recursive axiom-audit records are written under
`verification/local/`, which is ignored by Git. Individual commands are:

```sh
./scripts/unified_lake build PrimeIndependent.Solution
./scripts/unified_lake env lean ../../formal/independent/PrintAxioms.lean
```

Bootstrap is safe to rerun at the same pinned revisions. It rejects edited or
unexpected Git dependency checkouts. It never resets the working research
directory from which this release was prepared.

## Full independent reproduction

On macOS, after installing the prerequisites, run:

```sh
python3 scripts/reproduce.py
```

This installs the pinned verification tools, exports all dependencies into a
new source-only directory, checks that it contains no compiled Lean proof
artifacts, builds all Mathlib and upstream default targets plus the final
endpoints, replays the complete Solution import closure with
`leanchecker --fresh`, and runs Comparator with the Lean and nanoda kernels.
All three endpoints must pass in the same run. The source build and checker
stages disable proof caches, including when the ordinary build used `--cache`.
Lean's pinned compiler and bundled Init/Lean/Std/Lake remain the bootstrap
toolchain; the compiler and operating system are not rebuilt.

The complete workflow can take an hour or more. To retain another independent
run, choose a new directory with `--work-dir external/independent-another`.
To rebuild and recheck an interrupted prepared workspace, use `--resume`.
The runner refuses to overwrite a prepared workspace without that option.

The dual-kernel wrapper uses macOS Seatbelt and is tested on macOS. Linux users
can run the ordinary build; the bundled dual-kernel wrapper does not claim Linux
support. The source-only stages are also available separately:

```sh
python3 scripts/bootstrap.py
python3 scripts/prepare_verification_tools.py
python3 scripts/prepare_independent.py --work-dir external/independent-new
python3 scripts/build_independent.py
python3 scripts/replay_independent.py
python3 scripts/check_independent.py
python3 scripts/report_independent.py
```

## Paper and evidence

- [Announcement PDF](paper/primes-note.pdf) and [LaTeX source](paper/primes-note.tex).
- [Verification evidence](verification/README.md), including the original final
  three-endpoint run and its complete source-build baseline.
- [Third-party notices](THIRD_PARTY_NOTICES.md) and exact source revisions in
  [the dependency lock](dependencies.lock.json).

To rebuild the paper, install a TeX distribution and run:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error primes-note.tex
```

`v0.1-verified` identifies this private source release. The PDF is an announcement;
it does not claim to be the completed full-length paper.

