# Blast Radius — team Biomakers

Test selection for the RWX Blast Radius track (Builders Buildathon, Nov 2026).

For each patch against sqlglot `eb11aec`, `selector.py`:

1. Parses the diff and applies it in memory to the pinned source.
2. If the Python AST is unchanged (comments, formatting), selects nothing.
3. Otherwise maps every changed statement to the tests that execute it, using a
   per-test line-coverage map built from the pinned commit (`map/cov` inside `map.tgz`).
   Statements only run at import time (class tables, defaults, decorators) are
   resolved through the names they define and who reads them.
4. Fixture and test-file edits map to the tests that read or define them.
5. Packs the selected tests onto 1–8 workers (longest first) choosing the
   worker count with the lowest busiest-worker time + 2 s per worker.

`map.tgz` (unpacked to `map/` at build) is generated from the pinned commit only (coverage, imports, fixture
references); it contains no per-patch answers.
