# Verification evidence

`original/` contains the final recorded checks from the research workspace,
copied without editing their contents. No exploratory numerical experiments or
unsuccessful research runs are included.

The final three endpoints are `primeSum_time`, `primeCounting_time`, and
`primeFinding_time` in namespace `PrimeIndependent`. Their final run identifier
is `72ea63e4-8e5d-42d1-8468-2df02d7b3647`.

- `independent-chain.json` summarizes the successful three-endpoint build,
  complete fresh replay, Comparator statement comparison, and acceptance by
  both nanoda and the Lean kernel.
- `independent-clean-build.*`, `independent-fresh-replay.*`, and
  `independent-comparator.*` contain the final stage results and actual logs.
- `independent-preparation.json` and `independent-tools.json` record the source
  pins, tool versions, and bootstrap boundary.
- `source-build-baseline.*` contains the original full source build, including
  all 8,312 Mathlib source modules and the upstream default targets. This is
  retained because the final three-endpoint run reused those source-built
  dependencies. The baseline already built the prime-finding machine; the
  final run added its independent specification and repeated the full checking
  closure. It is not described as a second from-zero build.

Paths and timestamps inside these historical records are original provenance.
They can refer to the author's earlier working directory. They are not inputs
to the new reproduction scripts, and their old absolute paths need not exist
on another machine. The original baseline's old filename is represented here
by `source-build-baseline.json` and `source-build-baseline.log`.

New reproduction runs write to the ignored `local/` directory. [Release checks](release/checks.json) record successful initialization, the final
ordinary build and recursive axiom audit, a zero-artifact source-only export,
and PDF review. The 96 retained Lean files were compared directly with the
previously verified sources and are unchanged. This packaging run used the
pinned official Mathlib cache and existing pinned Git objects; it did not repeat
the complete from-zero source build or dual-kernel run. Those original results
remain in `original/`. All verification remains on one host unless another
party reproduces it.

