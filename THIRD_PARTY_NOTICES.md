# Third-party sources

The proof engine is downloaded from `anthropics/formal-math`, commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, under Apache License 2.0.
The bridge is downloaded from `xennygrimmato/eth-hamiltonicity`, commit
`41935962f954a4204446f4eddc438b3af6831722`, under the MIT license, with the
upstream exceptions described in its notices. Copies of the Apache license and
Tulsyan's MIT notice are retained in `LICENSES/`.

Downloaded upstream sources are not committed to this repository. The final
project modules in `formal/bridge/` extend the pinned bridge and are stored
separately from it. Bootstrap copies only the upstream bridge modules required
by the final proof import closure, then adds these project extensions.

Mathlib and its transitive dependencies retain their own licenses; their exact
Git revisions are listed in `dependencies.lock.json`. Comparator and lean4export
are fetched at pinned revisions by `scripts/prepare_verification_tools.py`.
nanoda is supplied by the pinned official Lean 4.35.0 distribution and is used
as a second kernel for the Lean 4.33.1 proof export.

No new open-source license is granted for the project's original material by
this release. Third-party licenses remain applicable to their material.

