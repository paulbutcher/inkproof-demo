# Inkproof.Demo design

## Theorem index and trusted computing base

`Inkproof.Demo.TheoremIndex`, `Tcb` and `Page` are native modules that do not import Lasm. `lake exe theorem-index <project dir> <output.html>` reads each pinned library's `API.lock` and sources from `<project dir>/.lake/packages`, so the page always describes the releases the demo is built against. A theorem links to its declaration at the library's tag, or to the module its namespaces name when it has no declaration of its own (a structure field, an instance). Line counts of generator templates, generated output and hand-written JavaScript shims are measured from the same sources.
